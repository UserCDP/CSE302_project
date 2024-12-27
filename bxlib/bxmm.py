# --------------------------------------------------------------------
import contextlib as cl
import hashlib

from typing import Optional as Opt

from .bxast   import *
from .bxscope import Scope
from .bxtac   import *

# ====================================================================
# Maximal munch

class MM:
    _counter = -1

    PRINTS = {
        Type.INT  : 'print_int',
        Type.BOOL : 'print_bool',
    }

    def __init__(self):
        self._proc    = None
        self._tac     = []
        self._scope   = Scope()
        self._loops   = []
        self._try_blocks = []

    tac = property(lambda self: self._tac)

    @staticmethod
    def mm(prgm: Program):
        mm = MM(); mm.for_program(prgm)
        return mm._tac

    @classmethod
    def fresh_temporary(cls):
        cls._counter += 1
        return f'%{cls._counter}'

    @classmethod
    def fresh_label(cls):
        cls._counter += 1
        return f'.L{cls._counter}'
    
    @staticmethod
    def exception_code(name: str) -> int:
        value = int(hashlib.sha256(name.encode()).hexdigest(), 16) & 0xFFFFFFFF
        if value > 0x7FFFFFFF:
            value -= 0x100000000
        return value

    def push(
        self,
        opcode     : str,
        *arguments : str | int,
        result     : Opt[str] = None,
    ):
        self._proc.tac.append(TAC(opcode, list(arguments), result))

    def push_label(self, label: str):
        self._proc.tac.append(f'{label}:')

    @cl.contextmanager
    def in_loop(self, labels: tuple[str, str]):
        self._loops.append(labels)
        try:
            yield
        finally:
            self._loops.pop()

    @cl.contextmanager
    def in_try_block(self, handler_label: str, end_label: str):
        self._try_blocks.append((handler_label, end_label))
        try:
            yield
        finally:
            self._try_blocks.pop()

    def set_exception(self, exception: str):
        if self._try_blocks:
            self.push('const', self.exception_code(exception.value), result = '@exception')
            self.push('jmp', self._try_blocks[-1][0])
        else:
            self.push('const', self.exception_code(exception.value), result = '@exception')

    def for_program(self, prgm: Program):
        self._tac.append(TACVar('exception', 0))
        for decl in prgm:
            match decl:
                case GlobVarDecl(name, init, type_):
                    assert(isinstance(init, IntExpression))
                    self._tac.append(TACVar(name.value, init.value))
                    self._scope.push(name.value, f'@{name.value}')

        for decl in prgm:
            match decl:
                case ProcDecl(name, arguments, retty, body):
                    assert(self._proc is None)
                    with self._scope.in_subscope():
                        arguments = list((x[0] for x in arguments))
                        # print("Args", arguments)

                        self._proc = TACProc(
                            name      = name.value,
                            arguments = [f'%{x.value}' for x in arguments],
                        )

                        for argument in arguments:
                            self._scope.push(argument.value, f'%{argument.value}')

                        self.for_statement(body)

                        if name.value == 'main':
                            self.for_statement(ReturnStatement(IntExpression(0)));

                        self._tac.append(self._proc)
                        self._proc = None

    def for_block(self, block: Block):
        with self._scope.in_subscope():
            if type(block) is not list:
                block = [block]
            for stmt in block:
                self.for_statement(stmt)

    def for_statement(self, stmt: Statement):
        match stmt:
            case VarDeclStatement(name, init):
                self._scope.push(name.value, self.fresh_temporary())
                temp = self.for_expression(init)
                self.push('copy', temp, result = self._scope[name.value])

            case AssignStatement(lhs, rhs):
                temp = self.for_expression(rhs)
                self.push('copy', temp, result = self._scope[lhs.value])

            case ExprStatement(expr):
                self.for_expression(expr)

            case IfStatement(condition, then, else_):
                tlabel = self.fresh_label()
                flabel = self.fresh_label()
                olabel = self.fresh_label()

                self.for_bexpression(condition, tlabel, flabel)
                self.push_label(tlabel)
                self.for_statement(then)
                self.push('jmp', olabel)
                self.push_label(flabel)
                if else_ is not None:
                    self.for_statement(else_)
                self.push_label(olabel)

            case WhileStatement(condition, body):
                clabel = self.fresh_label()
                blabel = self.fresh_label()
                olabel = self.fresh_label()

                with self.in_loop((clabel, olabel)):
                    self.push_label(clabel)
                    self.for_bexpression(condition, blabel, olabel)
                    self.push_label(blabel)
                    self.for_statement(body)
                    self.push('jmp', clabel)
                    self.push_label(olabel)

            case ContinueStatement():
                self.push('jmp', self._loops[-1][0])

            case BreakStatement():
                self.push('jmp', self._loops[-1][1])

            case BlockStatement(body):
                self.for_block(body)

            case ReturnStatement(expr):
                if expr is None:
                    self.push('ret')
                else:
                    temp = self.for_expression(expr)
                    self.push('ret', temp)

            case RaiseStatement(exception):
                self.set_exception(exception)
                if self._try_blocks:
                    self.push('jnz', '@exception', self._try_blocks[-1][0])
                else:
                    label = self.fresh_label()
                    self.push('jz', '@exception', label)
                    self.push('ret')
                    self.push_label(label)


            case TryExceptStatement(body, catches):
                handler_label = self.fresh_label()
                next_label = self.fresh_label()

                self._try_blocks.append((handler_label, next_label))

                self.for_statement(body)
                self.push_label(handler_label)

                for catch in catches:
                    exception_hash = self.exception_code(catch.exception.value)
                    temp = self.fresh_temporary()
                    self.push('const', exception_hash, result = temp)
                    self.push(OPCODES['subtraction'], '@exception', temp, result = temp)

                    next_handler_label = self.fresh_label()
                    self.push('jnz', temp, next_handler_label)

                    self.for_statement(catch.body)
                    self.push(OPCODES['bitwise-xor'], '@exception', '@exception', result = '@exception')
                    self.push('jmp', next_label)

                    self.push_label(next_handler_label)

                self._try_blocks.pop()
                if self._try_blocks:
                    self.push('jnz', '@exception', self._try_blocks[-1][0])
                else:
                    label = self.fresh_label()
                    self.push('jz', '@exception', label)
                    self.push('ret')
                    self.push_label(label)
                
                self.push_label(next_label)

            case _:
                assert(False)

    def for_expression(self, expr: Expression, force = False) -> str:
        target = None

        if not force and expr.type_ == Type.BOOL:
            target = self.fresh_temporary()
            tlabel = self.fresh_label()
            flabel = self.fresh_label()

            self.push('const', 0, result = target)
            self.for_bexpression(expr, tlabel, flabel)
            self.push_label(tlabel)
            self.push('const', 1, result = target)
            self.push_label(flabel)

        else:
            match expr:
                case VarExpression(name):
                    target = self._scope[name.value]

                case IntExpression(value):
                    target = self.fresh_temporary()
                    self.push('const', value, result=target)

                case OpAppExpression(operator, arguments):
                    target    = self.fresh_temporary()
                    arguments = [self.for_expression(e) for e in arguments]
                    self.push(OPCODES[operator], *arguments, result = target)

                case CallExpression(proc, arguments):
                    for i, argument in enumerate(arguments):
                        temp = self.for_expression(argument)
                        self.push('param', i+1, temp)
                    if expr.type_ != Type.VOID:
                        target = self.fresh_temporary()

                    self.push('call', proc.value, len(arguments), result=target)
                    # self.push('jnz', '@exception', 0)
                    if self._try_blocks:
                        self.push('jnz', '@exception', self._try_blocks[-1][0])
                    else:
                        label = self.fresh_label()
                        self.push('jz', '@exception', label)
                        self.push('ret')
                        self.push_label(label)

                case PrintExpression(argument):
                    # print(argument)
                    temp = self.for_expression(argument)
                    self.push('param', 1, temp)
                    proc = self.PRINTS[argument.type_]
                    self.push('call', proc, 1)

                case _:
                    assert(False)

        return target

    CMP_JMP = {
        'cmp-equal'                 : 'jz',
        'cmp-not-equal'             : 'jnz',
        'cmp-lower-than'            : 'jgt',
        'cmp-lower-or-equal-than'   : 'jge',
        'cmp-greater-than'          : 'jlt',
        'cmp-greater-or-equal-than' : 'jle',
    }

    def for_bexpression(self, expr: Expression, tlabel: str, flabel: str):
        assert(expr.type_ == Type.BOOL)

        match expr:
            case VarExpression(name):
                temp = self._scope[name.value]
                self.push('jz', temp, flabel)
                self.push('jmp', tlabel)

            case BoolExpression(True):
                self.push('jmp', tlabel)

            case BoolExpression(False):
                self.push('jmp', flabel)

            case OpAppExpression(
                    'cmp-equal'                |
                    'cmp-not-equal'            |
                    'cmp-lower-than'           |
                    'cmp-lower-or-equal-than'  |
                    'cmp-greater-than'         |
                    'cmp-greater-or-equal-than',
                    [e1, e2]):

                t1 = self.for_expression(e1)
                t2 = self.for_expression(e2)
                t  = self.fresh_temporary()
                self.push(OPCODES['subtraction'], t2, t1, result = t)

                self.push(self.CMP_JMP[expr.operator], t, tlabel)
                self.push('jmp', flabel)

            case OpAppExpression('boolean-and', [e1, e2]):
                olabel = self.fresh_label()
                self.for_bexpression(e1, olabel, flabel)
                self.push_label(olabel)
                self.for_bexpression(e2, tlabel, flabel)

            case OpAppExpression('boolean-or', [e1, e2]):
                olabel = self.fresh_label()
                self.for_bexpression(e1, tlabel, olabel)
                self.push_label(olabel)
                self.for_bexpression(e2, tlabel, flabel)

            case OpAppExpression('boolean-not', [e]):
                self.for_bexpression(e, flabel, tlabel)

            case CallExpression(_):
                temp = self.for_expression(expr, force = True)
                self.push('jz', temp, flabel)
                self.push('jmp', tlabel)

            case _:
                assert(False)