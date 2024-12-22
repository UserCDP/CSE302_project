# --------------------------------------------------------------------
import abc

from .bxtac import *

# --------------------------------------------------------------------
class AsmGen(abc.ABC):
    BACKENDS   = {}
    NAME       = None
    SYSTEM     = None
    MACHINE    = None

    def __init__(self):
        self._tparams = dict()
        self._temps   = dict()
        self._asm     = []

    def _temp(self, temp):
        if temp.startswith('@'):
            prelude, temp = self._format_temp(temp[1:])
        elif temp in self._tparams:
            prelude, temp = [], self._format_param(self._tparams[temp])
        else:
            index = self._temps.setdefault(temp, len(self._temps))
            prelude, temp = self._format_temp(index)
        for i in prelude:
            self._emit(*i)
        return temp

    @abc.abstractmethod
    def _format_temp(self, index):
        pass

    @abc.abstractmethod
    def _format_param(self, index):
        pass

    def __call__(self, instr: TAC | str):
        if isinstance(instr, str):
            self._asm.append(instr)
            return

        opcode = instr.opcode
        args   = instr.arguments[:]

        if instr.result is not None:
            args.append(instr.result)

        getattr(self, f'_emit_{opcode}')(*args)

    def _get_asm(self, opcode, *args):
        if not args:
            return f'\t{opcode}'
        return f'\t{opcode}\t{", ".join(args)}'

    def _get_label(self, lbl):
        return f'{lbl}:'

    def _emit(self, opcode, *args):
        self._asm.append(self._get_asm(opcode, *args))

    def _emit_label(self, lbl):
        self._asm.append(self._get_label(lbl))

    @classmethod
    def get_backend(cls, name):
        return cls.BACKENDS[name]

    @classmethod
    def select_backend(cls, system: str, machine: str):
        for backend in cls.BACKENDS.values():
            if system == backend.SYSTEM and machine == backend.MACHINE:
                return backend
        return None

    @classmethod    
    def register(cls, backend):
        cls.BACKENDS[backend.NAME] = backend

# --------------------------------------------------------------------
class AsmGen_x64_Linux(AsmGen):
    NAME    = 'x64-linux'
    SYSTEM  = 'Linux'
    MACHINE = 'x86_64'
    PARAMS  = ['%rdi', '%rsi', '%rdx', '%rcx', '%r8', '%r9']

    def __init__(self):
        super().__init__()
        self._params = []
        self._endlbl = None

    def _format_temp(self, index):
        if isinstance(index, str):
            return [], f'{index}(%rip)'
        return [], f'-{8*(index+1)}(%rbp)'

    def _format_param(self, index):
        return f'{8*(index+2)}(%rbp)'

    def _emit_const(self, ctt, dst):
        self._emit('movq', f'${ctt}', self._temp(dst))

    def _emit_copy(self, src, dst):
        self._emit('movq', self._temp(src), '%r11')
        self._emit('movq', '%r11', self._temp(dst))

    def _emit_alu1(self, opcode, src, dst):
        self._emit('movq', self._temp(src), '%r11')
        self._emit(opcode, '%r11')
        self._emit('movq', '%r11', self._temp(dst))

    def _emit_neg(self, src, dst):
        self._emit_alu1('negq', src, dst)

    def _emit_not(self, src, dst):
        self._emit_alu1('notq', src, dst)

    def _emit_alu2(self, opcode, op1, op2, dst):
        self._emit('movq', self._temp(op1), '%r11')
        self._emit(opcode, self._temp(op2), '%r11')
        self._emit('movq', '%r11', self._temp(dst))

    def _emit_add(self, op1, op2, dst):
        self._emit_alu2('addq', op1, op2, dst)

    def _emit_sub(self, op1, op2, dst):
        self._emit_alu2('subq', op1, op2, dst)

    def _emit_mul(self, op1, op2, dst):
        self._emit('movq', self._temp(op1), '%rax')
        self._emit('imulq', self._temp(op2))
        self._emit('movq', '%rax', self._temp(dst))

    def _emit_div(self, op1, op2, dst):
        self._emit('movq', self._temp(op1), '%rax')
        self._emit('cqto')
        self._emit('idivq', self._temp(op2))
        self._emit('movq', '%rax', self._temp(dst))

    def _emit_mod(self, op1, op2, dst):
        self._emit('movq', self._temp(op1), '%rax')
        self._emit('cqto')
        self._emit('idivq', self._temp(op2))
        self._emit('movq', '%rdx', self._temp(dst))

    def _emit_and(self, op1, op2, dst):
        self._emit_alu2('andq', op1, op2, dst)

    def _emit_or(self, op1, op2, dst):
        self._emit_alu2('orq', op1, op2, dst)

    def _emit_xor(self, op1, op2, dst):
        self._emit_alu2('xorq', op1, op2, dst)

    def _emit_shl(self, op1, op2, dst):
        self._emit('movq', self._temp(op1), '%r11')
        self._emit('movq', self._temp(op2), '%rcx')
        self._emit('salq', '%cl', '%r11')
        self._emit('movq', '%r11', self._temp(dst))

    def _emit_shr(self, op1, op2, dst):
        self._emit('movq', self._temp(op1), '%r11')
        self._emit('movq', self._temp(op2), '%rcx')
        self._emit('sarq', '%cl', '%r11')
        self._emit('movq', '%r11', self._temp(dst))

    def _emit_jmp(self, lbl):
        self._emit('jmp', lbl)

    def _emit_cjmp(self, cd, op, lbl):
        self._emit('cmpq', '$0', self._temp(op))
        self._emit(cd, lbl)

    def _emit_jz(self, op, lbl):
        self._emit_cjmp('jz', op, lbl)

    def _emit_jnz(self, op, lbl):
        self._emit_cjmp('jnz', op, lbl)

    def _emit_jlt(self, op, lbl):
        self._emit_cjmp('jl', op, lbl)

    def _emit_jle(self, op, lbl):
        self._emit_cjmp('jle', op, lbl)

    def _emit_jgt(self, op, lbl):
        self._emit_cjmp('jg', op, lbl)

    def _emit_jge(self, op, lbl):
        self._emit_cjmp('jge', op, lbl)

    def _emit_param(self, i, arg):
        assert(len(self._params)+1 == i)
        self._params.append(arg)

    def _emit_call(self, lbl, arg, ret = None):
        assert(arg == len(self._params))

        for i, x in enumerate(self._params[:6]):
            self._emit('movq', self._temp(x), self.PARAMS[i])

        qarg = 0 if arg <= 6 else arg - 6

        if qarg & 0x1:
            self._emit('subq', '$8', '%rsp')

        for x in self._params[6:][::-1]:
            self._emit('pushq', self._temp(x))

        self._emit('callq', lbl)

        if qarg > 0:
            self._emit('addq', f'${qarg + qarg & 0x1}', '%rsp')

        if ret is not None:
            self._emit('movq', '%rax', self._temp(ret))

        self._params = []

    def _emit_ret(self, ret = None):
        if ret is not None:
            self._emit('movq', self._temp(ret), '%rax')
        self._emit('jmp', self._endlbl)

    def _emit_raise(self, exception):
        self._emit('mov', exception, '%rax')
        self._emit('jmp', '@exception_handler')

    def _emit_try(self, start, end):
        self._emit_label(start)
        self._emit_label(end)

    @classmethod
    def lower1(cls, tac: TACProc | TACVar) -> list[str]:
        emitter = cls()

        match tac:
            case TACVar(name, init):
                emitter._emit('.data')
                emitter._emit('.globl', name)
                emitter._emit_label(name)
                emitter._emit('.quad', str(init))

                return emitter._asm

            case TACProc(name, arguments, ptac):
                emitter._endlbl = f'.E_{name}'

                for i in range(min(6, len(arguments))):
                    emitter._emit('movq', emitter.PARAMS[i], emitter._temp(arguments[i]))

                for i, arg in enumerate(arguments[6:]):
                    emitter._tparams[arg] = i

                for instr in ptac:
                    emitter(instr)

                nvars  = len(emitter._temps)
                nvars += nvars & 1

                return [
                    emitter._get_asm('.text'),
                    emitter._get_asm('.globl', name),
                    emitter._get_label(name),
                    emitter._get_asm('pushq', '%rbp'),
                    emitter._get_asm('movq', '%rsp', '%rbp'),
                    emitter._get_asm('subq', f'${8*nvars}', '%rsp'),
                ] + emitter._asm + [
                    emitter._get_label(emitter._endlbl),
                    emitter._get_asm('movq', '%rbp', '%rsp'),
                    emitter._get_asm('popq', '%rbp'),
                    emitter._get_asm('retq'),
                ]

    @classmethod
    def lower(cls, tacs: list[TACProc | TACVar]) -> str:
        aout = [cls.lower1(tac) for tac in tacs]
        aout = [x for tac in aout for x in tac]
        return "\n".join(aout) + "\n"

AsmGen.register(AsmGen_x64_Linux)

# --------------------------------------------------------------------
class AsmGen_arm64_Darwin(AsmGen):
    NAME    = 'arm64-apple-darwin'
    SYSTEM  = 'Darwin'
    MACHINE = 'arm64'
    PARAMS   = list(f'X{i}' for i in range(7+1))

    def __init__(self):
        super().__init__()
        self._params = []
        self._endlbl = None

    def _format_temp(self, index):
        if isinstance(index, str):
            return [
                ('adrp', 'X15', f'_{index}@PAGE'),
            ], f'[X15, _{index}@PAGEOFF]'
        
        index = 8*(index+1)
        if index > 256:
            return [
                ('sub', 'X15', 'FP', f'#{index}')
            ], '[X15]'

        return [], f'[FP, #-{index}]'

    def _format_param(self, index):
        return f'[FP, #{8*(index+2)}]'

    def _emit_const(self, ctt, dst):
        if ctt < 0:
            ctt = (1 << 64) + ctt
        self._emit('movz', 'X9', f'#{ctt & 0xffff}')
        ctt, i = (ctt >> 16), 1
        while ctt != 0:
            self._emit('movk', 'X9', f'#{ctt & 0xffff}', f'lsl {16*i}')
            ctt >>= 16; i += 1
        self._emit('str', 'X9', self._temp(dst))

    def _emit_copy(self, src, dst):
        self._emit('ldr', 'X9', self._temp(src))
        self._emit('str', 'X9', self._temp(dst))

    def _emit_alu1(self, opcode, op, dst):
        self._emit('ldr', 'X9', self._temp(op))
        self._emit(opcode, 'X10', 'X9')
        self._emit('str', 'X10', self._temp(dst))

    def _emit_neg(self, src, dst):
        self._emit_alu1('neg', src, dst)

    def _emit_not(self, src, dst):
        self._emit_alu1('mvn', src, dst)

    def _emit_alu2(self, opcode, op1, op2, dst):
        self._emit('ldr', 'X9', self._temp(op1))
        self._emit('ldr', 'X10', self._temp(op2))
        self._emit(opcode, 'X11', 'X9', 'X10')
        self._emit('str', 'X11', self._temp(dst))

    def _emit_add(self, op1, op2, dst):
        self._emit_alu2('add', op1, op2, dst)
        
    def _emit_sub(self, op1, op2, dst):
        self._emit_alu2('sub', op1, op2, dst)

    def _emit_mul(self, op1, op2, dst):
        self._emit_alu2('mul', op1, op2, dst)

    def _emit_div(self, op1, op2, dst):
        self._emit_alu2('sdiv', op1, op2, dst)

    def _emit_mod(self, op1, op2, dst):
        self._emit('ldr' , 'X9', self._temp(op1))
        self._emit('ldr' , 'X10', self._temp(op2))
        self._emit('sdiv', 'X11', 'X9', 'X10')
        self._emit('mul' , 'X11', 'X11', 'X10')
        self._emit('sub' , 'X11', 'X9', 'X11')
        self._emit('str' , 'X11', self._temp(dst))

    def _emit_and(self, op1, op2, dst):
        self._emit_alu2('and', op1, op2, dst)

    def _emit_or(self, op1, op2, dst):
        self._emit_alu2('orr', op1, op2, dst)

    def _emit_xor(self, op1, op2, dst):
        self._emit_alu2('eor', op1, op2, dst)

    def _emit_shl(self, op1, op2, dst):
        self._emit_alu2('lsl', op1, op2, dst)

    def _emit_shr(self, op1, op2, dst):
        self._emit_alu2('lsr', op1, op2, dst)

    def _emit_jmp(self, lbl):
        self._emit('b', lbl)

    def _emit_jz(self, op, lbl):
        self._emit('ldr', 'X9', self._temp(op))
        self._emit('cbz', 'X9', lbl)
        
    def _emit_jnz(self, op, lbl):
        self._emit('ldr', 'X9', self._temp(op))
        self._emit('cbnz', 'X9', lbl)

    def _emit_jlt(self, op, lbl):
        self._emit('ldr', 'X9', self._temp(op))
        self._emit('cmp', 'X9', '#0')
        self._emit('b.lt', lbl)

    def _emit_jle(self, op, lbl):
        self._emit('ldr', 'X9', self._temp(op))
        self._emit('cmp', 'X9', '#0')
        self._emit('b.le', lbl)

    def _emit_jgt(self, op, lbl):
        self._emit('ldr', 'X9', self._temp(op))
        self._emit('cmp', 'X9', '#0')
        self._emit('b.gt', lbl)

    def _emit_jge(self, op, lbl):
        self._emit('ldr', 'X9', self._temp(op))
        self._emit('cmp', 'X9', '#0')
        self._emit('b.ge', lbl)

    def _emit_param(self, i, arg):
        assert(len(self._params)+1 == i)
        self._params.append(arg)

    def _emit_call(self, lbl, arg, ret = None):
        assert(arg == len(self._params))

        nstack = max(0, arg - len(self.PARAMS))
        nstack = 0 if nstack == 0 else (nstack - 1) // 2 + 1

        self._emit('sub', 'SP', 'SP', f'#{16 * nstack}')
        self._emit('mov', 'X9', 'SP')

        for i, x in enumerate(self._params[len(self.PARAMS):]):
            self._emit('ldr', 'X10', self._temp(x))
            self._emit('str', 'X10', f'[X9, #{8*i}]')

        for i, x in enumerate(self._params[:len(self.PARAMS)]):
            self._emit('ldr', self.PARAMS[i], self._temp(x))

        self._emit('bl', '_' + lbl)

        self._emit('add', 'SP', 'SP', f'#{16 * nstack}')

        if ret is not None:
            self._emit('str', 'X0', self._temp(ret))

        self._params = []

    def _emit_ret(self, ret = None):
        if ret is not None:
            self._emit('ldr', 'X0', self._temp(ret))
        self._emit('b', self._endlbl)

    def _emit_raise(self, exception):
        self._emit('mov', exception, '%rax')
        self._emit('jmp', '@exception_handler')

    def _emit_try(self, start, end):
        self._emit_label(start)
        self._emit_label(end)

    @classmethod
    def lower1(cls, tac: TACProc | TACVar) -> list[str]:
        emitter = cls()

        match tac:
            case TACVar(name, init):
                emitter._emit('.data')
                emitter._emit('.globl', name)
                emitter._emit_label('_' + name)
                emitter._emit('.quad', str(init))

                return emitter._asm

            case TACProc(name, arguments, ptac):
                emitter._endlbl = f'.E_{name}'

                for i in range(min(len(emitter.PARAMS), len(arguments))):
                    emitter._emit('str', emitter.PARAMS[i], emitter._temp(arguments[i]))

                for i, arg in enumerate(arguments[len(emitter.PARAMS):]):
                    emitter._tparams[arg] = i

                for instr in ptac:
                    emitter(instr)

                nvars  = len(emitter._temps)
                nvars += nvars & 1

                return [
                    emitter._get_asm('.text'),
                    emitter._get_asm('.globl', '_' + name),
                    emitter._get_label('_' + name),
                    emitter._get_asm('stp' , 'FP', 'LR', '[SP, #-16]!'),
                    emitter._get_asm('mov', 'FP', 'SP'),
                    emitter._get_asm('sub', 'SP', 'SP', f'#{8*nvars}'),
                ] + emitter._asm + [
                    emitter._get_label(emitter._endlbl),
                    emitter._get_asm('mov', 'SP', 'FP'),
                    emitter._get_asm('ldp', 'FP', 'LR', '[SP]', '#16'),
                    emitter._get_asm('ret'),
                ]

    @classmethod
    def lower(cls, tacs: list[TACProc | TACVar]) -> str:
        aout = [cls.lower1(tac) for tac in tacs]
        aout = [x for tac in aout for x in tac]
        return "\n".join(aout) + "\n"

AsmGen.register(AsmGen_arm64_Darwin)
