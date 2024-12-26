# --------------------------------------------------------------------
import dataclasses as dc

from typing import Optional as Opt

# ====================================================================
# Three-Address Code

OPCODES = {
    'opposite'            : 'neg',
    'addition'            : 'add',
    'subtraction'         : 'sub',
    'multiplication'      : 'mul',
    'division'            : 'div',
    'modulus'             : 'mod',
    'bitwise-negation'    : 'not',
    'bitwise-and'         : 'and',
    'bitwise-or'          :  'or',
    'bitwise-xor'         : 'xor',
    'logical-left-shift'  : 'shl',
    'logical-right-shift' : 'shr',
}

# --------------------------------------------------------------------
@dc.dataclass
class TAC:
    opcode    : str
    arguments : list[str | int]
    result    : Opt[str | int] = None
    exception : Opt[str] = None

    def tojson(self):
        return dict(
            opcode = self.opcode   ,
            args   = self.arguments,
            result = self.result   ,
        )

    def __repr__(self):
        aout = self.opcode
        if self.arguments:
            aout = f"{aout} {', '.join(map(repr, self.arguments))}"
        if self.result:
            aout = f"{self.result} = {aout}"
        return aout

# --------------------------------------------------------------------
class TACProc:
    __match_args__ = ('name', 'arguments', 'tac')

    def __init__(self, name: str, arguments: list[str]):
        self.name      = name
        self.arguments = arguments
        self.tac       = []

    def __repr__(self):
        aout = f"proc @{self.name}"
        if self.arguments:
            aout = f"{aout}({', '.join(map(repr, self.arguments))})"
        aout = [f"{aout}:"]
        for tac in self.tac:
            aout.append(f"    {tac};")
        return "\n".join(aout) + "\n"

# --------------------------------------------------------------------
class TACVar:
    __match_args__ = ('name', 'value')

    def __init__(self, name: str, value: int):
        self.name  = name
        self.value = value

    def __repr__(self):
        return f"var @{self.name} = {self.value};"


class RaiseStmt(TAC):
    def __init__(self, exception, lineno):
        self.opcode = 'raise'
        self.arguments = [exception]
        self.result = None
        self.lineno = lineno

    def __repr__(self):
        return f"raise {self.arguments[0]}"

class TryExceptStmt(TAC):
    def __init__(self, try_block, exception, handler, lineno):
        self.opcode = 'tryexcept'
        self.arguments = [try_block, exception, handler]
        self.result = None
        self.lineno = lineno

    def __repr__(self):
        return f"try {self.arguments[0]} except {self.arguments[1]}"

class TAC:
    def __init__(self, opcode, arguments, result=None):
        self.opcode = opcode
        self.arguments = arguments
        self.result = result

    def __repr__(self):
        return f"{self.result} = {self.opcode} {', '.join(map(str, self.arguments))}"
