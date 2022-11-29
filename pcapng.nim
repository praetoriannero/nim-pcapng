import algorithm
import os
import math
import nimpy
import streams
import strformat
import strutils
import system
import std/times

# https://www.ietf.org/archive/id/draft-tuexen-opsawg-pcapng-03.html
# https://stackoverflow.com/questions/17928319/whats-the-difference-between-a-pcap-file-with-a-magic-number-of-0x4d3cb2a1-an

const
    optEndofopt = 0x0000
    BYTE_ORDER = 0x1A2B3C4D
    SHB = 0x0A0D0D0A                    # Section Header Block
    IDB = 0x00000001                    # Interface Description Block
    EPB = 0x00000006                    # Enhanced Packet Block
    SPB = 0x00000003                    # Simple Packet Block
    NRB = 0x00000004                    # Name Resolution Block
    ISB = 0x00000005                    # Interface Statistics Block
    SJB = 0x00000009                    # systemd Journal Export Block
    DSB = 0x0000000A                    # Decryption Secrets Block
    CB1 = 0x00000BAD                    # Custom Block
    CB2 = 0x40000BAD                    # Custom Block
    nrbRecordEnd = 0x0000
    # nrbRecordIpv4 = 0x0001
    # nrbRecordIpv6 = 0x0002

type
    BigEndianStream* = object of FileStreamObj
        lef: File

    Option* = object
        optionCode*: int16
        optionLength*: int16
        optionValue*: seq[uint8]

    NameResolutionRecord* = object
        recordType*: int32
        recordLength*: int32
        recordValue*: seq[uint8]

    SectionHeaderBlock* = object
        blockType*: int32
        blockTotalLength*: int32
        byteOrder*: int32
        majorVersion*: int16
        minorVersion*: int16
        sectionLength*: int64
        options*: seq[Option]

    InterfaceDescriptionBlock* = object
        blockType*: int32
        blockTotalLength*: int32
        linkType*: int16
        reserved*: int16
        snapLen*: int32
        options*: seq[Option]

    EnhancedPacketBlock* = object
        blockType*: int32
        blockTotalLength*: int32
        interfaceId*: int32
        timestampHigh*: int32
        timestampLow*: int32
        capturedPacketLength*: int32
        originalPacketLength*: int32
        packetData*: seq[uint8]
        options*: seq[Option]

    InterfaceStatisticsBlock* = object
        blockType*: int32
        blockTotalLength*: int32
        interfaceId*: int32
        timestampHigh*: int32
        timestampLow*: int32
        options*: seq[Option]

    SimplePacketBlock* = object
        blockType*: int32
        blockTotalLength*: int32
        originalPacketLength*: int32
        packetData*: seq[uint8]

    NameResolutionBlock* = object
        blockType*: int32
        blockTotalLength*: int32
        records*: seq[NameResolutionRecord]
        options*: seq[Option]

    SystemdJournalExportBlock* = object
        blockType*: int32
        blockTotalLength*: int32
        journalEntry*: seq[uint8]

    DecryptionSecretsBlock* = object
        blockType*: int32
        blockTotalLength*: int32
        secretsType*: int32
        secretsLength*: int32
        secretsData*: seq[uint8]
        options*: seq[Option]

    SecretKind* = enum
        ZigBeeAPSKey,
        ZigBeeNWKKey

    SecretType* = object
        case kind: SecretKind
        of ZigBeeNWKKey:
            nwkKey: int32
        of ZigBeeAPSKey:
            apsKey: int32

    CustomBlock* = object
        blockType*: int32
        blockTotalLength*: int32
        privateEnterpriseNumber*: int32
        customData*: seq[uint8]
        options*: seq[Option]

    UnknownBlock* = object
        blockType*: int32
        blockTotalLength*: int32

    EntryType = enum
        sectionHeaderBlock,
        interfaceDescriptionBlock,
        enhancedPacketBlock,
        simplePacketBlock,
        nameResolutionBlock,
        interfaceStatisticsBlock,
        systemdJournalExportBlock,
        decryptionSecretsBlock,
        customBlock

    Entry* = object
        case entryType: EntryType
        of sectionHeaderBlock:
            shb: SectionHeaderBlock
        of interfaceDescriptionBlock:
            idb: InterfaceDescriptionBlock
        of enhancedPacketBlock:
            epb: EnhancedPacketBlock
        of simplePacketBlock:
            spb: SimplePacketBlock
        of nameResolutionBlock:
            nrb: NameResolutionBlock
        of interfaceStatisticsBlock:
            isb: InterfaceStatisticsBlock
        of systemdJournalExportBlock:
            sje: SystemdJournalExportBlock
        of decryptionSecretsBlock:
            dsb: DecryptionSecretsBlock
        of customBlock:
            cb: CustomBlock

proc swapEndian[T](value: var T): T {.inline.} =
    var tempArr: array[sizeof(T), uint8]
    tempArr = cast[array[sizeof(T), byte]](value)
    tempArr.reverse()
    return cast[T](tempArr)

proc swapEndian(buffer: ptr) {.inline.} =
    var tempArr: array[sizeof(buffer[]), byte]
    tempArr = cast[array[sizeof(buffer[]), byte]](buffer[])
    tempArr.reverse()
    buffer[] = cast[typeof(buffer[])](tempArr)

proc skipPad*(stream: Stream) =
    var
        currentPos = stream.getPosition()
        newPos: int
    
    newPos = currentPos + ((4 - currentPos mod 4) mod 4)
    stream.setPosition(newPos)

proc skipBlock*(stream: Stream) {.inline.} =
    # Skip the current block and advance file stream to next available entry
    var blockLen: int32

    stream.read(blockLen)
    stream.read(blockLen)

    discard stream.readStr(blockLen - 8)

proc parseOptions*(stream: Stream): seq[Option] =
#                      1                   2                   3
#  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
# +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# |      Option Code              |         Option Length         |
# +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# /                       Option Value                            /
# /              variable length, padded to 32 bits               /
# +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# /                                                               /
# /                 . . . other options . . .                     /
# /                                                               /
# +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# |   Option Code == opt_endofopt |   Option Length == 0          |
# +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    var
        optCode: int16
        optionLen: int16
        optionVal: seq[uint8]
        optionByte: uint8
        shbOption: Option

    optCode = stream.readInt16()
    optionLen = stream.readInt16()

    if optionLen <= 0 or optCode == optEndofopt:
        var beginning: int = stream.getPosition() - 4
        stream.setPosition(beginning)
        return result

    while optCode != optEndofopt and optionLen > 0:
        optionVal.newSeq(optionLen)
        # stream.read(optionVal)
        for i in 0 ..< optionLen:
            # optionVal[i] = stream.readUint8()
            stream.read(optionByte)
            optionVal[i] = optionByte

        shbOption = Option(
            optionCode: optCode,
            optionLength: optionLen,
            optionValue: optionVal)

        stream.skipPad()
        result.add(shbOption)
        optCode = stream.readInt16()
        optionLen = stream.readInt16()

proc parseNameResolutionRecords*(stream: Stream): seq[NameResolutionRecord] =
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  0 |      Record Type              |      Record Value Length      |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  4 /                       Record Value                            /
#    /              variable length, padded to 32 bits               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    .                                                               .
#    .                  . . . other records . . .                    .
#    .                                                               .
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    |  Record Type = nrb_record_end |   Record Value Length = 0     |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    var
        recType: int16
        recValLen: int16
        recVal: seq[uint8]

    recType = stream.readInt16()
    recValLen = stream.readInt16()

    while recType != nrbRecordEnd:
        recVal.newSeq(recValLen)
        for i in 0 ..< recValLen:
            recVal[i] = stream.readUint8()
        
        var nrbRecord = NameResolutionRecord(
            recordType: recType,
            recordLength: recValLen,
            recordValue: recVal
        )

        result.add(nrbRecord)
        stream.skipPad()

        recType = stream.readInt16()
        recValLen = stream.readInt16()


proc newSectionHeaderBlock*(stream: Stream): SectionHeaderBlock =
#                         1                   2                   3
#     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  0 |                   Block Type = 0x0A0D0D0A                     |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  4 |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  8 |                      Byte-Order Magic                         |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 12 |          Major Version        |         Minor Version         |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 16 |                                                               |
#    |                          Section Length                       |
#    |                                                               |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 24 /                                                               /
#    /                      Options (variable)                       /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    var
        blockTypeVal: int32
        blockTotalLen: int32
        byteOrderVal: int32
        majorVersionVal: int16
        minorVersionVal: int16
        sectionLengthVal: int64
        blockLengthValidation: int64

        optionsSeq: seq[Option]

    blockTypeVal = stream.readInt32()

    doAssert blockTypeVal == SHB

    blockTotalLen = stream.readInt32()
    byteOrderVal = stream.readInt32()

    doAssert byteOrderVal == BYTE_ORDER

    majorVersionVal = stream.readInt16()
    minorVersionVal = stream.readInt16()
    sectionLengthVal = stream.readInt64()

    optionsSeq = parseOptions(stream)

    blockLengthValidation = stream.readInt32()

    doAssert blockLengthValidation == blockTotalLen

    result = SectionHeaderBlock(
        blockType: blockTypeVal,
        byteOrder: byteOrderVal,
        majorVersion: majorVersionVal,
        minorVersion: minorVersionVal,
        sectionLength: sectionLengthVal,
        options: optionsSeq,
        blockTotalLength: blockTotalLen
    )


proc newInterfaceStatisticsBlock*(stream: Stream): InterfaceStatisticsBlock = 
#                         1                   2                   3
#     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  0 |                   Block Type = 0x00000005                     |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  4 |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  8 |                         Interface ID                          |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 12 |                        Timestamp (High)                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 16 |                        Timestamp (Low)                        |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 20 /                                                               /
#    /                      Options (variable)                       /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    var
        blockTypeVal: int32
        blockTotalLen: int32
        iface: int32
        tstampHigh: int32
        tstampLow: int32
        optionsSeq: seq[Option]
        blockLengthValidation: int32

    blockTypeVal = stream.readInt32()

    doAssert blockTypeVal == ISB

    blockTotalLen = stream.readInt32()
    iface = stream.readInt32()
    tstampHigh = stream.readInt32()
    tstampLow = stream.readInt32()
    optionsSeq = parseOptions(stream)
    stream.skipPad()

    blockLengthValidation = stream.readInt32()

    doAssert blockLengthValidation == blockTotalLen

    result = InterfaceStatisticsBlock(
        blockType: blockTypeVal,
        blockTotalLength: blockTotalLen,
        interfaceId: iface,
        timestampHigh: tstampHigh,
        timestampLow: tstampLow,
        options: optionsSeq
    )

proc newInterfaceDescriptionBlock*(stream: Stream): InterfaceDescriptionBlock =
#                         1                   2                   3
#     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  0 |                    Block Type = 0x00000001                    |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  4 |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  8 |           LinkType            |           Reserved            |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 12 |                            SnapLen                            |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 16 /                                                               /
#    /                      Options (variable)                       /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    var
        blockTypeVal: int32
        blockTotalLen: int32
        link: int16
        reserve: int16
        snap: int32
        optionsSeq: seq[Option]
        blockLengthValidation: int32

    blockTypeVal = stream.readInt32()

    doAssert blockTypeVal == IDB

    blockTotalLen = stream.readInt32()
    link = stream.readInt16()
    reserve = stream.readInt16()
    snap = stream.readInt32()

    optionsSeq = parseOptions(stream)

    blockLengthValidation = stream.readInt32()

    doAssert blockLengthValidation == blockTotalLen

    result = InterfaceDescriptionBlock(
        blockType: blockTypeVal,
        blockTotalLength: blockTotalLen,
        linkType: link,
        reserved: reserve,
        snapLen: snap,
        options: optionsSeq
    )

    
proc newEnhancedPacketBlock*(stream: Stream): EnhancedPacketBlock =
#                         1                   2                   3
#     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  0 |                    Block Type = 0x00000006                    |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  4 |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  8 |                         Interface ID                          |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 12 |                        Timestamp (High)                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 16 |                        Timestamp (Low)                        |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 20 |                    Captured Packet Length                     |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 24 |                    Original Packet Length                     |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 28 /                                                               /
#    /                          Packet Data                          /
#    /              variable length, padded to 32 bits               /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    /                                                               /
#    /                      Options (variable)                       /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    # let
    #     blockTypeVal: int32
    #     blockTotalLen: int32
    #     iface: int32
    #     tstampHigh: int32
    #     tstampLow: int32
    #     capPacketLen: int32
    #     ogPacketLen: int32
    #     blockLengthValidation: int32
        
    var
        optionsSeq: seq[Option]
        packet: seq[uint8]

    let blockTypeVal = stream.readInt32()
    # discard stream.readInt32()

    # doAssert blockTypeVal == EPB

    let blockTotalLen = stream.readInt32()
    let iface = stream.readInt32()
    let tstampHigh = stream.readInt32()
    let tstampLow = stream.readInt32()
    let capPacketLen = stream.readInt32()
    let ogPacketLen = stream.readInt32()
    
    packet.newSeq(capPacketLen)
    for i in 0 ..< capPacketLen:
        packet[i] = stream.readUint8()

    stream.skipPad()

    let blockLengthValidation = stream.readInt32()

    doAssert blockLengthValidation == blockTotalLen

    return EnhancedPacketBlock(
        blockType: blockTypeVal,
        blockTotalLength: blockTotalLen,
        interfaceId: iface,
        timestampHigh: tstampHigh,
        timestampLow: tstampLow,
        capturedPacketLength: capPacketLen,
        originalPacketLength: ogPacketLen,
        packetData: packet,
        options: optionsSeq
    )


proc newSimplePacketBlock*(stream: Stream): SimplePacketBlock =
#                         1                   2                   3
#     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  0 |                    Block Type = 0x00000003                    |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  4 |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  8 |                    Original Packet Length                     |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 12 /                                                               /
#    /                          Packet Data                          /
#    /              variable length, padded to 32 bits               /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    var
        blockTypeVal: int32
        blockTotalLen: int32
        ogPacketLen: int32
        packet: seq[uint8]
        blockLengthValidation: int32

    blockTypeVal = stream.readInt32()

    doAssert blockTypeVal == SPB

    blockTotalLen = stream.readInt32()
    packet.newSeq(ogPacketLen)
    for i in 0 ..< ogPacketLen:
        packet[i] = stream.readUint8()

    stream.skipPad()

    blockLengthValidation = stream.readInt32()

    doAssert blockLengthValidation == blockTotalLen

    result = SimplePacketBlock(
        blockType: blockTypeVal,
        blockTotalLength: blockTotalLen,
        originalPacketLength: ogPacketLen,
        packetData: packet
    )


proc newNameResolutionBlock*(stream: Stream): NameResolutionBlock =
#                         1                   2                   3
#     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  0 |                    Block Type = 0x00000004                    |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  4 |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  8 |      Record Type              |      Record Value Length      |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 12 /                       Record Value                            /
#    /              variable length, padded to 32 bits               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    .                                                               .
#    .                  . . . other records . . .                    .
#    .                                                               .
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    |  Record Type = nrb_record_end |   Record Value Length = 0     |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    /                                                               /
#    /                      Options (variable)                       /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    var
        blockTypeVal: int32
        blockTotalLen: int32
        recs: seq[NameResolutionRecord]
        opts: seq[Option]

    blockTypeVal = stream.readInt32()

    doAssert blockTypeVal == NRB

    blockTotalLen = stream.readInt32()
    recs = parseNameResolutionRecords(stream)
    opts = parseOptions(stream)

    doAssert stream.readInt32() == blockTotalLen

    result = NameResolutionBlock(
        blockType: blockTypeVal,
        blockTotalLength: blockTotalLen,
        records: recs,
        options: opts
    )


proc newSystemdJournalExportBlock*(stream: Stream): SystemdJournalExportBlock =
#                         1                   2                   3
#     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  0 |                    Block Type = 0x00000009                    |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  4 |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  8 /                                                               /
#    /                         Journal Entry                         /
#    /              variable length, padded to 32 bits               /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    var
        blockTypeVal: int32
        blockTotalLen: int32
        journalLen: int32
        journal: seq[uint8]

    blockTypeVal = stream.readInt32()

    doAssert blockTypeVal == SJB

    blockTotalLen = stream.readInt32()

    journalLen = blockTotalLen - 12

    journal.newSeq(journalLen)
    for i in 0 ..< journalLen:
        journal[i] = stream.readUint8()

    stream.skipPad()

    result = SystemdJournalExportBlock(
        blockType: blockTypeVal,
        blockTotalLength: blockTotalLen,
        journalEntry: journal
    )


proc newDecryptionSecretsBlock*(stream: Stream): DecryptionSecretsBlock =
#                         1                   2                   3
#     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  0 |                   Block Type = 0x0000000A                     |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  4 |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  8 |                          Secrets Type                         |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 12 |                         Secrets Length                        |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 16 /                                                               /
#    /                          Secrets Data                         /
#    /              (variable length, padded to 32 bits)             /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    /                                                               /
#    /                       Options (variable)                      /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    /                       Block Total Length                      /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    # var
    #     blockTypeVal: int32
    #     blockTotalLen: int32
    #     secretType: int32
    #     secretsLen: int32
    stream.skipBlock()
    result = DecryptionSecretsBlock()


proc newCustomBlock*(stream: Stream): CustomBlock =
#                         1                   2                   3
#     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  0 |             Block Type = 0x00000BAD or 0x40000BAD             |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  4 |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#  8 |                Private Enterprise Number (PEN)                |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
# 12 /                                                               /
#    /                          Custom Data                          /
#    /              variable length, padded to 32 bits               /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    /                                                               /
#    /                      Options (variable)                       /
#    /                                                               /
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
#    |                      Block Total Length                       |
#    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    stream.skipBlock()
    result = CustomBlock()


iterator iterPcapngEntries*(pcapPath: string): Entry =
    let
        stream = newFileStream(pcapPath)
    defer:
        stream.close()

    var
        blockType: int32
        shbCount: int
        idbCount: int
        epbCount: int
        spbCount: int
        isbCount: int
        sjeCount: int
        dsCount: int
        custCount: int

        sectionHeaderBlock: SectionHeaderBlock
        interfaceDescriptionBlock: InterfaceDescriptionBlock
        nameResolutionBlock: NameResolutionBlock
        enhancedPacketBlock: EnhancedPacketBlock
        simplePacketBlock: SimplePacketBlock
        interfaceStatisticsBlock: InterfaceStatisticsBlock
        systemdJournalExportBlock: SystemdJournalExportBlock
        decryptionSecretsBlock: DecryptionSecretsBlock
        customBlock: CustomBlock
        entry: Entry

    while not stream.atEnd():
        stream.peek(blockType)
        # echo(blockType)
        case blockType:
            of SHB:
                sectionHeaderBlock = stream.newSectionHeaderBlock()
                shbCount += 1
                entry = Entry(
                    entryType: EntryType.sectionHeaderBlock,
                    shb: sectionHeaderBlock
                )
            of IDB:
                interfaceDescriptionBlock = stream.newInterfaceDescriptionBlock()
                idbCount += 1
                entry = Entry(
                    entryType: EntryType.interfaceDescriptionBlock,
                    idb: interfaceDescriptionBlock
                )
            of NRB:
                nameResolutionBlock = stream.newNameResolutionBlock()
                entry = Entry(
                    entryType: EntryType.nameResolutionBlock,
                    nrb: nameResolutionBlock
                )
            of EPB:
                enhancedPacketBlock = stream.newEnhancedPacketBlock()
                epbCount += 1
                entry = Entry(
                    entryType: EntryType.enhancedPacketBlock,
                    epb: enhancedPacketBlock
                )
            of SPB:
                simplePacketBlock = stream.newSimplePacketBlock()
                spbCount += 1
                entry = Entry(
                    entryType: EntryType.simplePacketBlock,
                    spb: simplePacketBlock
                )
            of ISB:
                interfaceStatisticsBlock = stream.newInterfaceStatisticsBlock()
                isbCount += 1
                entry = Entry(
                    entryType: EntryType.interfaceStatisticsBlock,
                    isb: interfaceStatisticsBlock
                )
            of SJB:
                systemdJournalExportBlock = stream.newSystemdJournalExportBlock()
                sjeCount += 1
                entry = Entry(
                    entryType: EntryType.systemdJournalExportBlock,
                    sje: systemdJournalExportBlock
                )
            of DSB:
                decryptionSecretsBlock = stream.newDecryptionSecretsBlock()
                dsCount += 1
                entry = Entry(
                    entryType: EntryType.decryptionSecretsBlock,
                    dsb: decryptionSecretsBlock
                )
            of CB1:
                customBlock = stream.newCustomBlock()
                custCount += 1
                entry = Entry(
                    entryType: EntryType.customBlock,
                    cb: customBlock
                )
            of CB2:
                customBlock = stream.newCustomBlock()
                custCount += 1
                entry = Entry(
                    entryType: EntryType.customBlock,
                    cb: customBlock
                )
            else:
                echo(&"Block type {blockType} not implemented. Skipping!")
                stream.skipBlock()

        # echo(entry)
        yield entry

proc skipBlock*(f: File, swapEndianness: bool) =
    # Skip the current block and advance file stream to next available entry
    var
        blockLen: int32
        bytesRead: int
        readError: ref IOError

    bytesRead = f.readBuffer(blockLen.addr, 4)
    if bytesRead != 4:
        new(readError)
        readError.msg = "Reached EOF"
        raise readError

    if swapEndianness:
        blockLen = blockLen.swapEndian()

    var skippedBytes = newString(blockLen - 8)
    discard readBuffer(f, addr(skippedBytes[0]), blockLen - 8)

proc skipPad*(f: File, bufferLen: uint32): int {.inline, discardable.} =
    var
        padLen: uint = (4 - bufferLen mod 4) mod 4
        skippedBytes = newString(padLen)

    if padLen == 0:
        return

    return readBuffer(f, addr(skippedBytes[0]), padLen)

type
    EpbData = object
        iface: uint32
        tstampHigh: uint32
        tstampLow: uint32
        capPacketLen: uint32
        ogPacketLen: uint32

    ShbData = object
        byteOrderMagic: uint32
        majorVersion: uint16
        minorVersion: uint16
        sectionLength: uint64

    EndianAwareReader = object
        file: File
        endian: Endianness

proc readBuffer(reader: EndianAwareReader, buffer: ptr, len: Natural): int {.inline, discardable.} =
    result = readBuffer(reader.file, buffer, len)
    if reader.endian != cpuEndian:
        buffer.swapEndian()

proc matchesHostEndian(reader: EndianAwareReader): bool {.inline.} =
    return reader.endian == cpuEndian

proc newBlock[T](reader: EndianAwareReader): T {.inline.} =
    if not reader.matchesHostEndian():
        for field, value in result.fieldPairs():
            reader.readBuffer(addr(value), sizeof(value))
    else:
        reader.readBuffer(addr(result), sizeof(T))

iterator readPackets*(pcapPath: string): seq[byte] {.exportpy.} =
    var 
        f = open(pcapPath, fmRead)
        reader: EndianAwareReader = EndianAwareReader(file: f, endian: cpuEndian)
        bytesRead: int
        blockTypeVal: int32
        packetData: seq[byte]
        blockTotalLen: int32
        epb: EpbData
        shb: ShbData
        skipLen: int
        shbEndianness: Endianness
        byteDump: array[2^16, byte]

    while true:
        bytesRead = reader.readBuffer(addr(blockTypeVal), sizeof(blockTypeVal))
        if bytesRead != sizeof(blockTypeVal):
            break

        reader.readBuffer(addr(blockTotalLen), sizeof(blockTotalLen))

        case blockTypeVal:
            of EPB:
                epb = newBlock[EpbData](reader)

                packetData.newSeq(epb.capPacketLen)
                reader.readBuffer(addr(packetData[0]), epb.capPacketLen)

                skipLen = blockTotalLen - int(sizeof(blockTypeVal)  + sizeof(blockTotalLen) + sizeof(epb) + epb.capPacketLen)

                reader.readBuffer(addr(byteDump[0]), skipLen)

                yield packetData
            of SHB:
                shb = newBlock[ShbData](reader)

                if shb.byteOrderMagic == BYTE_ORDER:
                    shbEndianness = littleEndian
                else:
                    shbEndianness = bigEndian

                if reader.endian != shbEndianness:
                    for field, value in shb.fieldPairs():
                        addr(value).swapEndian()

                    addr(blockTotalLen).swapEndian()
                    reader.endian = shbEndianness

                skipLen = blockTotalLen - (sizeof(blockTypeVal) + sizeof(shb) + sizeof(blockTotalLen))

                reader.readBuffer(addr(byteDump[0]), skipLen)

            else:
                skipLen = blockTotalLen - (sizeof(blockTypeVal) + sizeof(blockTotalLen))
                reader.readBuffer(addr(byteDump[0]), skipLen)

when isMainModule:
    var args = commandLineParams()
    if len(args) != 1:
        var error: ref IOError
        new(error)
        error.msg = "one argument is allowed: file path"
        raise error

    var
        pcapName = args[0]
        totalPackets: int
        elapsedTime: float
        pktsPerSecond: float

    let time = cpuTime()

    for entry in readPackets(pcapName):
        totalPackets += 1

    elapsedTime = cpuTime() - time
    pktsPerSecond = float(totalPackets) / elapsedTime

    echo(&"Completed in {elapsedTime} seconds")
    echo(&"{pktsPerSecond} blocks read per second")
    echo(&"{totalPackets} total packets found")
