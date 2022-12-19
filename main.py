"""

0	LDC c	c ⟶ Acc
1	LDV a	< a > ⟶ Acc
2	STV a	Acc ⟶ < a >
3	ADD a	Acc + < a > ⟶ Acc
4	AND a	Acc AND < a > ⟶ Acc
5	OR a	Acc OR < a > ⟶ Acc
6	XOR a	Acc XOR < a > ⟶ Acc
7	EQL a	if(Acc == < a >) { -1 ⟶ Acc } else { 0 ⟶ Acc }
8	JMP a	Jump to address a
9	JMN a	Jump to address a if Acc < 0
A	LDIV a	<< a >> ⟶ Acc
B	STIV a	Acc ⟶ << a >>
C	JMS a	jump subroutine
D	JIND a	jump indirect
E		free
F0	HALT	stops the minimal machine
F1	NOT	one's complement(Acc) ⟶ Acc
F2	RAR	rotates Acc on the the right ⟶ Acc
F3 - FF		free
"""
import enum
import pprint
from typing import *
from pyparsing import *

import pyparsing
from z3 import *

PROGRAM_SIZE = 16
MEM_SIZE = 16
MAX_STEPS = 16
BV_SIZE = 8


class Op(enum.Enum):
    LDC = 0
    LDV = 1
    STV = 2
    ADD = 3
    AND = 4
    OR = 5
    XOR = 6
    EQL = 7
    JMP = 8
    JMN = 9
    LDIV = 10
    STIV = 11
    JMS = 12
    JIND = 13
    FREE = 14
    HALT = 15
    NOT = 16
    RAR = 17
    NOP = 18

    LBL = 19
    UNUSED = 20
    MAX = 0xF3


Program: List[Tuple[Op, BitVecRef]]


def is_valid_opcode(op):
    return Op.LDC <= op < Op.UNUSED


def val(x: int):
    return BitVecVal(x & 0xFF, BV_SIZE)


def var(name: str):
    return BitVecVal(name, BV_SIZE)


BV_SORT = BitVecSort(BV_SIZE)
ZERO = val(0)
MINUS_ONE = val(-1)


def interpret(program):
    acc: BitVecRef = val(0)
    pc: int = 0

    memory = Array("memory", BV_SORT, BV_SORT)

    for i in range(MEM_SIZE):
        memory = Store(memory, val(i), ZERO)
    # memory = [var(f"mem_{i}") for i in range(MEM_SIZE)]

    for step in range(MAX_STEPS):
        if not (0 <= pc < len(program)):
            print("Invalid program counter")
            return acc, memory

        opcode, arg = program[pc]
        # __CPROVER_assume(0 <= pc & & pc < PROGRAM_SIZE);
        # __CPROVER_assume(is_valid_opcode(op));

        match opcode:
            case Op.LDC:  # LDC c    c ⟶ Acc
                acc = val(arg & 0xFF)
                pc += 1
            case Op.LDV:  # LDV a    < a > ⟶ Acc
                acc = Select(memory, arg)
                pc += 1
            case Op.STV:  # STV a    Acc ⟶ < a >
                memory = Store(memory, val(arg), acc)
                pc += 1
            case Op.ADD:  # ADD a Acc + < a > ⟶ Acc
                acc = acc + Select(memory, val(arg))
                pc += 1
            case Op.AND:  # AND a Acc AND < a > ⟶ Acc
                acc = acc & Select(memory, val(arg))
                pc += 1
            case Op.OR:  # OR a   Acc OR < a > ⟶ Acc
                acc = acc & Select(memory, val(arg))
                pc += 1
            case Op.XOR:  # XOR a Acc XOR < a > ⟶ Acc
                acc = acc ^ Select(memory, val(arg))
                pc += 1
            case Op.EQL:  # EQL a if (Acc == < a >) {-1 ⟶ Acc} else {0 ⟶ Acc}
                if acc == memory[arg]:
                    acc = MINUS_ONE
                else:
                    acc = ZERO
                pc += 1
            case Op.JMP:  # JMP a Jump to address a
                pc = arg
            case Op.JMN:  # JMN a Jump to address a if Acc < 0
                if acc < 0:
                    pc = arg
                else:
                    pc += 1
            case Op.LDIV:  # LDIV a << a >> ⟶ Acc
                # TODO correct effect ?
                # tmp = state.get(arg)
                # throw away bits above address range...
                # tmp = state.get(tmp & Constants.ADDRESS_MASK)
                # builder.set(State.ACCU, tmp)
                # builder.incIAR()
                acc = Select(memory, Select(memory, arg))
                pc += 1
            case Op.STIV:  # STIV a  Acc ⟶ << a >>
                # TODO Correct effect ?
                memory = Store(memory, Select(memory, arg), acc)
                pc += 1
                # tmp = state.get(arg)
                # builder.set(tmp & Constants.ADDRESS_MASK, state.get(State.ACCU))
                # builder.incIAR()
            case Op.JMS:  # JMS a jump subroutine
                # builder.set(arg, state.get(State.IAR) + 1)
                # builder.set(State.IAR, (arg + 1) & Constants.ADDRESS_MASK)
                # __CPROVER_assume(false); // TODO
                # Effect is unclear
                pc += 1
                break
            case Op.JIND:  # JIND a jump indirect
                # __CPROVER_assume(false); // TODO
                # Effect is unclear
                # // builder.set(State.IAR, state.get(arg) & Constants.ADDRESS_MASK)
                pc += 1
                break
            case Op.HALT:  # HALT stops the minimal machine
                return acc, memory

            case Op.NOT:  # NOT one's complement(Acc) ⟶ Acc
                acc = ~acc
                pc += 1

            case Op.RAR:  # RAR rotates Acc on the right ⟶ Acc
                acc = (acc >> 1) | ((acc & 1) << 7)
                pc += 1

            case Op.NOP:
                pc += 1

    assert program[pc][0] == Op.HALT
    return acc, memory


def parser(input: str):
    program = []

    def add_label(input, pos, result: ParseResults):
        label = result[0]
        program.append((Op.LBL, label))

    def add_op_int(input, pos, result: ParseResults):
        cmd = result[0]
        arg = result[2]
        program.append((Op.__dict__[cmd], int(arg)))

    def add_op_noarg(input, pos, result: ParseResults):
        cmd = result[0]
        program.append((Op.__dict__[cmd], None))

    def add_op_jump(input, pos, result: ParseResults):
        cmd = result[0]
        lbl = result[2]
        program.append((Op.__dict__[cmd], lbl))

    label = Word(alphas)

    integer = Optional('-') + Word(pyparsing.nums)
    num_cmds = [Keyword(x)
                for x in ('LDC', 'LDV', 'STV', 'ADD', 'AND',
                          'OR', 'XOR', 'EQL', 'LDIV', 'STIV')]
    no_arg_cmds = [Keyword('HALT'), Keyword('NOT'), Keyword('RAR')]
    jump_cmd_names = [Keyword(x) for x in ('EQL', 'JMP', 'JMN', 'JMS', 'JIND')]

    nl = Literal("\n")
    comment = (';' + ZeroOrMore(~nl) + nl)
    skip = White() | comment
    skipO = Optional(skip)
    label_mark = skipO + (label + ":").addParseAction(add_label)
    cmd = (MatchFirst(no_arg_cmds).addParseAction(add_op_noarg)
           | (MatchFirst(num_cmds) + skip + integer).addParseAction(add_op_int)
           | (MatchFirst(jump_cmd_names) + skip + label).addParseAction(add_op_jump))
    file = ZeroOrMore(skipO + (label_mark | cmd)) + OneOrMore(skip) + StringEnd()

    file.parse_string(input)

    jump_table = {}
    for idx, (op, arg) in enumerate(program):
        if op == Op.LBL:
            jump_table[arg] = idx
            # remove mark
            program[idx] = (Op.NOP, None)

    for idx, (op, arg) in enumerate(program):
        if op in (Op.JMP, Op.JMS, Op.JMS, Op.JIND, Op.EQL):
            program[idx] = (op, jump_table[arg])

    return program


if __name__ == '__main__':
    P = parser("""
    A: LDC 1
       STV 0 
       LDC 2
       HALT
    """)
    pprint.pprint(P)
    c = 10
    s = Solver()
    acc, mem = interpret(P)
    s.add(Select(mem, val(0)) != val(1))
    s.add(acc != val(2))
    print(s.to_smt2())
    print(s.check())