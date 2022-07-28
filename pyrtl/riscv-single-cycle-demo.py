import pyrtl
from generate_ir import generate_ir
from enum import IntEnum

class Opcode(IntEnum):
    """These numbers come from Table 24.1 of the RISC-V ISA Manual, Volume 1"""

    LOAD = 0b0000011
    IMM = 0b0010011
    AUIPC = 0b0010111
    STORE = 0b0100011
    REG = 0b0110011
    LUI = 0b0110111
    BRANCH = 0b1100011
    JALR = 0b1100111
    JAL = 0b1101111
    SYSTEM = 0b1110011

class ALUOp(IntEnum):
    AND = 0x0
    SLL = 0x1
    SLT = 0x2
    SLTU = 0x3
    XOR = 0x4
    SRL = 0x5
    OR = 0x6
    ADD = 0x7
    SUB = 0x8
    SRA = 0xD
    IMM = 0xE
    NOP = 0xF

class MaskMode(IntEnum):
    BYTE = 0x0
    SHORT = 0x1
    WORD = 0x2

class RegWriteSrc(IntEnum):
    ALU = 0b0
    PC = 0b1

class ImmType(IntEnum):
    R = 0
    I = 1
    S = 2
    B = 3
    U = 4
    J = 5

class JumpTarget(IntEnum):
    IMM = 0
    ALU = 1

def unimplemented_control(op, fn3, fn7):
    return (
        pyrtl.net_hole("cont_imm_type_hole", 3, op, fn3, fn7),
        pyrtl.net_hole("cont_jump_hole", 1, op, fn3, fn7),
        pyrtl.net_hole("cont_target_hole", 1, op, fn3, fn7),
        pyrtl.net_hole("cont_branch_hole", 1, op, fn3, fn7),
        pyrtl.net_hole("cont_branch_inv_hole", 1, op, fn3, fn7),
        pyrtl.net_hole("cont_reg_write_hole", 1, op, fn3, fn7),
        pyrtl.net_hole("cont_reg_write_src_hole", 1, op, fn3, fn7),
        pyrtl.net_hole("cont_mem_write_hole", 1, op, fn3, fn7),
        pyrtl.net_hole("cont_mem_read_hole", 1, op, fn3, fn7),
        pyrtl.net_hole("cont_alu_imm_hole", 1, op, fn3, fn7),
        pyrtl.net_hole("cont_alu_pc_hole", 1, op, fn3, fn7),
        pyrtl.net_hole("cont_alu_op_hole", 4, op, fn3, fn7),
        pyrtl.net_hole("cont_mask_mode_hole", 2, op, fn3, fn7),
        pyrtl.net_hole("cont_mem_sign_ext_hole", 1, op, fn3, fn7),
    )

def add_wire(wire, bitwidth=None, name="", block=None):
    """Creates a new wire driven by the wire."""
    bitwidth = bitwidth if bitwidth is not None else len(wire)
    named_wire = pyrtl.WireVector(bitwidth=bitwidth, name=name, block=block)
    named_wire <<= wire
    return named_wire


def add_register(wire, bitwidth=None, name="", block=None):
    """Creates a new register driven by the wire."""
    bitwidth = bitwidth if bitwidth is not None else len(wire)
    register = pyrtl.Register(bitwidth=bitwidth, name=name, block=block)
    register.next <<= wire
    return register

def alu(op, in1, in2):
    """The ALU logic for the RV processor

    :param alu_op: the operation the ALU should perform
    :param alu_in1: the first input
    :param alu_in2: the second input

    :return: the result of the computation
    """
    op = add_wire(op, bitwidth=5, name="alu_op")
    in1 = add_wire(in1, bitwidth=32, name="alu_in1")
    in2 = add_wire(in2, bitwidth=32, name="alu_in2")

    out = pyrtl.WireVector(bitwidth=32, name="alu_out")
    out <<= pyrtl.enum_mux(
        op,
        {
            ALUOp.ADD: in1 + in2,
            ALUOp.SUB: in1 - in2,
            ALUOp.SLL: pyrtl.shift_left_logical(in1, in2[0:5]),
            ALUOp.SLT: pyrtl.signed_lt(in1, in2),
            ALUOp.SLTU: in1 < in2,
            ALUOp.XOR: in1 ^ in2,
            ALUOp.SRL: pyrtl.shift_right_logical(in1, in2[0:5]),
            ALUOp.SRA: pyrtl.shift_right_arithmetic(in1, in2[0:5]),
            ALUOp.OR: in1 | in2,
            ALUOp.AND: in1 & in2,
            ALUOp.IMM: in2,
        },
        default=0,
    )

    return out

def insert_nop(fn7, rs2, rs1, fn3, rd, op, nop):
    return (
        pyrtl.mux(nop, fn7, pyrtl.Const(0, bitwidth=len(fn7))),
        pyrtl.mux(nop, rs2, pyrtl.Const(0, bitwidth=len(rs2))),
        pyrtl.mux(nop, rs1, pyrtl.Const(0, bitwidth=len(rs1))),
        pyrtl.mux(nop, fn3, pyrtl.Const(0, bitwidth=len(fn3))),
        pyrtl.mux(nop, rd, pyrtl.Const(0, bitwidth=len(rd))),
        pyrtl.mux(nop, op, pyrtl.Const(Opcode.REG, bitwidth=len(op))),
    )

def decode_inst(inst, nop=None):
    """Decodes fetched instruction, inserting a nop if a bubble is needed.

    :param inst: the input full encoded RISC-V instruction
    :param nop: a control signal indicating if a nop should be inserted
    :return: a tuple containing the components (funct7, rs2, rs1, funct3, rd, opcode)
    """

    # fetch inst and decode
    fn7, rs2, rs1, fn3, rd, op = pyrtl.chop(inst, 7, 5, 5, 3, 5, 7)

    if nop is None:
        return fn7, rs2, rs1, fn3, rd, op
    else:
        fn7, rs2, rs1, fn3, rd, op = insert_nop(fn7=fn7, rs2=rs2, rs1=rs1, fn3=fn3, rd=rd, op=op, nop=nop)
        return fn7, rs2, rs1, fn3, rd, op

def get_immediate(inst, imm_type):
    """Takes a RISC-V instruction and returns the sign-exteneded immediate value.

    Note that different RISC-V instruction types have different bits used as the immediate.
    Also, for the B type and J type instructions, the values are *already* shifted
    left on the output.

    See Volume 1 of the RISC-V Manual, Figures 2.3 and 2.4

    :param inst: the input full encoded RISC-V instruction
    :param imm_type: the immediate format of the instruction (R, I, S, etc.)
    :return: the output sign-extended immediate value encoded in the instruction
    """

    imm = pyrtl.WireVector(bitwidth=32, name="inst_imm")
    imm <<= pyrtl.enum_mux(
        imm_type,
        {
            ImmType.I: inst[20:].sign_extended(32),
            ImmType.S: pyrtl.concat(inst[25:], inst[7:12]).sign_extended(32),
            ImmType.B: pyrtl.concat(
                inst[31], inst[7], inst[25:31], inst[8:12], 0
            ).sign_extended(32),
            ImmType.U: pyrtl.concat(inst[12:], pyrtl.Const(0, bitwidth=12)),
            ImmType.J: pyrtl.concat(
                inst[31], inst[12:20], inst[20], inst[21:31], 0
            ).sign_extended(32),
        },
        default=0,
    )

    return imm

def inst_memory(pc):
    """Instruction memory IOs:

    :param pc: the program counter
    :return inst_mem: a reference to the memory block
    :return inst: the fetched instruction (inst_mem[pc])
    """
    inst_mem = pyrtl.MemBlock(
        bitwidth=32, addrwidth=32, name="imem", asynchronous=True
    )

    # The addresses in instruction memory are word-addressable, while the addresses produced by
    # alu operations with the immediates, pcs, etc. are byte-addressable, so we need to shift
    # the address given by two to the right to get the word address
    inst = pyrtl.WireVector(bitwidth=32, name="inst")
    inst <<= inst_mem[pyrtl.shift_right_logical(pc, 2)]
    return inst_mem, inst


def data_memory(addr, write_data, read, write, mask_mode, sign_ext):
    """The data memory

    :param addr: memory address to access
    :param write_data: data to write to addr
    :param mem_read: control signal for reading
    :param mem_write: control signal for writing
    :param mask_mode: inst[12:14] (i.e. lower two bits of fn3)
        0x10 means word (see lw/sw), 0x00 and 0x01 are byte, halfword respectively
    :param sign_ext: inst[14] (i.e. upper bit of funct3)
        1 means its lb/lh, 0 means its lbu/lhu

    :return: data read from addr
    """
    addr = add_wire(addr, bitwidth=32, name="mem_addr")
    write_data = add_wire(write_data, bitwidth=32, name="mem_write_data")
    read = add_wire(read, bitwidth=1, name="mem_read")
    write = add_wire(write, bitwidth=1, name="mem_write")
    mask_mode = add_wire(mask_mode, bitwidth=2, name="mem_mask_mode")
    sign_ext = add_wire(sign_ext, bitwidth=1, name="mem_sign_ext")

    data_mem = pyrtl.MemBlock(
        bitwidth=32, addrwidth=32, name="dmem", asynchronous=True
    )

    real_addr = pyrtl.shift_right_arithmetic(addr, 2)
    offset = addr[0:2]  # lower 2 bits determine if its byte 0, 1, 2, or 3 of word
    read_data = data_mem[real_addr]

    # Store: write the particular byte/halfword/word to memory and maintain
    # the other bytes (in the class of byte/halfword) already present
    to_write = pyrtl.WireVector(len(write_data))
    with pyrtl.conditional_assignment:
        with mask_mode == MaskMode.BYTE:
            with offset == 0:
                to_write |= pyrtl.concat(read_data[8:32], write_data[0:8])
            with offset == 1:
                to_write |= pyrtl.concat(
                    read_data[16:32], write_data[0:8], read_data[0:8]
                )
            with offset == 2:
                to_write |= pyrtl.concat(
                    read_data[24:32], write_data[0:8], read_data[0:16]
                )
            with pyrtl.otherwise:
                to_write |= pyrtl.concat(write_data[0:8], read_data[0:24])
        with mask_mode == MaskMode.SHORT:
            with offset == 0:
                to_write |= pyrtl.concat(read_data[16:32], write_data[0:16])
            with offset == 1:  # illegal non-aligned write
                to_write |= pyrtl.concat(
                    read_data[24:32], write_data[0:16], read_data[0:8]
                )
            with pyrtl.otherwise:
                to_write |= pyrtl.concat(write_data[0:16], read_data[0:16])
        with pyrtl.otherwise:
            to_write |= write_data

    data_mem[real_addr] <<= pyrtl.MemBlock.EnabledWrite(to_write, write)

    # Load
    read_data_ext = pyrtl.WireVector(len(read_data), name="mem_read_data")
    with pyrtl.conditional_assignment:
        with mask_mode == MaskMode.BYTE:
            read_data_shift = pyrtl.shift_right_logical(
                read_data, pyrtl.concat(offset, pyrtl.Const(0, bitwidth=3))
            )[0:8]
            read_data_ext |= pyrtl.select(
                sign_ext,
                read_data_shift.sign_extended(len(read_data)),
                read_data_shift.zero_extended(len(read_data)),
            )
        with mask_mode == MaskMode.SHORT:
            read_data_shift = pyrtl.shift_right_logical(
                read_data, pyrtl.concat(offset, pyrtl.Const(0, bitwidth=3))
            )[0:16]
            read_data_ext |= pyrtl.select(
                sign_ext,
                read_data_shift.sign_extended(len(read_data)),
                read_data_shift.zero_extended(len(read_data)),
            )
        with pyrtl.otherwise:  # whole word, and sign-extending is meaningless
            read_data_ext |= read_data

    return add_wire(read_data_ext, name="READ_DATA_EXT")

def reg_file(rs1, rs2, rd, write_data, write):
    """Register file IOs:

    :param rs1: the number of the register to read
    :param rs2: the number of the register to read
    :param rd: the number of the register to write
    :param write_data: the data to write into R[rd]
    :param reg_write: write enable; if true, write the rd register
    :return rs1_val: the data in register number rs1 (R[rs1])
    :return rs2_val: the data in register number rs2 (R[rs2])

    Basic operation:
    - rs1_val = R[rs1]
    - rs2_val = R[rs2]
    - if (reg_write) R[rd] = write_data
    """
    rs1 = add_wire(rs1, bitwidth=5, name="rf_rs1")
    rs2 = add_wire(rs2, bitwidth=5, name="rf_rs2")
    rd = add_wire(rd, bitwidth=5, name="rf_rd")
    write_data = add_wire(write_data, bitwidth=32, name="rf_write_data")
    write = add_wire(write, bitwidth=1, name="rf_write")

    # PyRTL defaults to all memories having value 0. By disallowing
    # writing to the zero register with the condition in the EnabledWrite below,
    # the zero register is essentially hardwired to zero.

    # Read async, write sync
    # NOTE: When async=False, PyRTL complains about the read-addresses not being ready,
    # since it doesn't know at this point that they're Inputs or Registers
    rf = pyrtl.MemBlock(bitwidth=32, addrwidth=5, name="rf", asynchronous=True)
    rf[rd] <<= pyrtl.MemBlock.EnabledWrite(write_data, write & (rd != 0))

    rs1_val = pyrtl.WireVector(bitwidth=32, name="rf_rs1_val")
    rs2_val = pyrtl.WireVector(bitwidth=32, name="rf_rs2_val")
    rs1_val <<= pyrtl.select(rs1 == 0, pyrtl.Const(0, bitwidth=32), rf[rs1])
    rs2_val <<= pyrtl.select(rs2 == 0, pyrtl.Const(0, bitwidth=32), rf[rs2])

    return rs1_val, rs2_val

def cpu(control, flush=None):
    pc = pyrtl.wire.Register(bitwidth=32, name="pc")  # program counter
    pc_plus_4 = add_wire(pc + 4, len(pc))  # program counter plus four

    # fetch inst and decode
    inst_mem, inst = inst_memory(pc=pc)
    inst_fn7, inst_rs2, inst_rs1, inst_fn3, inst_rd, inst_op = decode_inst(
        inst, nop=None
    )

    # define control block
    (
        cont_imm_type,  # (3) type of instruction (R, I, S, etc.)
        cont_jump,  # (1) unconditional jump is taken
        cont_target,  # (1) jump to immediate or alu_out
        cont_branch,  # (1) conditional branch is taken
        cont_branch_inv,  # (1) branch is taken if alu_out != 0
        cont_reg_write,  # (1) register rd is updated
        cont_reg_write_src,  # (1) write alu_out or pc+4 to rd
        cont_mem_write,  # (1) write to memory
        cont_mem_read,  # (1) read from memory
        cont_alu_imm,  # (1) alu_in2 from register or immediate
        cont_alu_pc,  # (1) alu_in1 from register or pc
        cont_alu_op,  # (4) alu operation to use
        cont_mask_mode,  # (2) whether to r/w byte, short, or word
        cont_mem_sign_ext,  # (1) zero extend read_data
    ) = control(op=inst_op, fn3=inst_fn3, fn7=inst_fn7)

    # parse immediate
    inst_imm = get_immediate(inst, cont_imm_type)

    # register file
    reg_write_data = pyrtl.WireVector(bitwidth=32)
    rs1_val, rs2_val = reg_file(
        rs1=inst_rs1,
        rs2=inst_rs2,
        rd=inst_rd,
        write_data=reg_write_data,
        write=cont_reg_write | cont_mem_read,  # if read memory, always write
    )

    # alu block
    alu_out = alu(
            op=cont_alu_op,
            in1=pyrtl.mux(cont_alu_pc, rs1_val, pc),
            in2=pyrtl.mux(cont_alu_imm, rs2_val, inst_imm))

    # data memory
    read_data = data_memory(
        addr=alu_out,
        write_data=rs2_val,
        read=cont_mem_read,
        write=cont_mem_write,
        mask_mode=cont_mask_mode,
        sign_ext=cont_mem_sign_ext,
    )

    # write to register file
    reg_write_data <<= pyrtl.mux(
        cont_mem_read,
        pyrtl.enum_mux(
            cont_reg_write_src, {RegWriteSrc.ALU: alu_out, RegWriteSrc.PC: pc_plus_4}
        ),
        read_data,
    )

    # update pc
    taken = add_wire(
        cont_jump | (cont_branch & ((alu_out == 0) ^ cont_branch_inv)), name="taken"
    )
    target = pyrtl.enum_mux(
        cont_target, {JumpTarget.IMM: pc + inst_imm, JumpTarget.ALU: alu_out}
    )
    if flush is None:
        flush = pyrtl.Const(0, bitwidth=1)
    with pyrtl.conditional_assignment:
        with flush:
            pc.next |= pc
        with taken:
            pc.next |= target
        with pyrtl.otherwise:
            pc.next |= pc_plus_4

    return inst_mem  # return ref to instruction memory unit

cpu(control=unimplemented_control)
pyrtl.optimize()
ir = generate_ir("riscv", pyrtl.working_block())
print(ir)
