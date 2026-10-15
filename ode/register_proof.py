"""Explicit six-register arithmetic-machine semantics and reduction proofs.

This is a total abstract machine with six initialized Word32 registers,
straight-line ADD/XOR/immediate-ROR instructions, and no memory or flags.
It is not an AArch64 decoder or an ISA refinement theorem.
"""
from .canon import hash_of,parse
from .arx_proof import theory as arithmetic_theory
from .ground_proof import Evaluation
from .xor32_proof import app,equation,var

REGISTERS = ('a','b','c','d','x','y')


def theory(bit_theory):
    t=arithmetic_theory(bit_theory)
    constructors=[ [var('reg-'+r),[]] for r in REGISTERS ]
    t[2].append([var('Register'),constructors])
    t[2].append([var('State'),[[var('state'),[var('Word32')]*6]]])
    instructions=[[var(op),[var('Register')]*3] for op in ('add-register','xor-register')]
    instructions += [[var(f'rotate-register-{n}'),[var('Register')]*2] for n in range(32)]
    t[2].append([var('Instruction'),instructions])
    t[2].append(parse('(Program ((halt ()) (next (Instruction Program))))'))
    fields=[var('s'+r) for r in REGISTERS]
    for i,r in enumerate(REGISTERS):
        t[4].append([var('state-'+r),parse('((s State))'),var('Word32'),
                     [[var('state'),fields,fields[i]]]])
    read_cases=[[var('reg-'+r),[],app('state-'+r,var('s'))] for r in REGISTERS]
    t[4].append([var('read-register'),parse('((r Register) (s State))'),var('Word32'),read_cases])
    write_cases=[]
    for r in REGISTERS:
        body=app('state',*[var('v') if q==r else app('state-'+q,var('s')) for q in REGISTERS])
        write_cases.append([var('reg-'+r),[],body])
    t[4].append([var('write-register'),parse('((r Register) (v Word32) (s State))'),var('State'),write_cases])
    d,a,b,s=map(var,('d','a','b','s'))
    read=lambda r:app('read-register',r,s)
    cases=[]
    for op,word_op in (('add-register','add32'),('xor-register','xor32')):
        body=app('write-register',d,app(word_op,read(a),read(b)),s)
        cases.append([var(op),[d,a,b],body])
    for n in range(32):
        body=app('write-register',d,app(f'ror-{n}',read(a)),s)
        cases.append([var(f'rotate-register-{n}'),[d,a],body])
    t[4].append([var('step'),parse('((i Instruction) (s State))'),var('State'),cases])
    t[4].append(parse('''(run ((p Program) (s State)) State
        ((halt () s) (next (i tail) (run tail (step i s)))))'''))
    return t


def program(instructions):
    result=app('halt')
    for instruction in reversed(instructions):
        result=app('next',instruction,result)
    return result


def initial_state():
    return app('state',*[var(r) for r in REGISTERS])


def prove_execution(t, instructions, expected):
    """Prove a symbolic execution against a separately supplied final state.

    All six initial words are arbitrary. Expected expressions must name
    those same variables. Definitions are reduced, not algebraically
    normalized: arithmetic expressions remain explicit symbolic values.
    """
    left=app('run',program(instructions),initial_state())
    p=Evaluation(t)
    result,last=p.evaluate(left)
    assert result==expected, 'expected state differs from definition reduction'
    p.trans(last,p.refl(expected))
    params=[[var(r),var('Word32')] for r in REGISTERS]
    goal=[var('goal'),3,hash_of(t),params,equation(left,expected)]
    proof=[var('proof'),3,hash_of(goal),[],[var('derive'),p.steps]]
    return goal,proof


def g_instructions():
    """The 14 register operations of BLAKE3 G, with x/y preserved."""
    reg=lambda r:app('reg-'+r)
    add=lambda d,a,b:app('add-register',reg(d),reg(a),reg(b))
    xor=lambda d,a,b:app('xor-register',reg(d),reg(a),reg(b))
    rotate=lambda d,n:app(f'rotate-register-{n}',reg(d),reg(d))
    return [add('a','a','b'),add('a','a','x'),xor('d','d','a'),rotate('d',16),
            add('c','c','d'),xor('b','b','c'),rotate('b',12),
            add('a','a','b'),add('a','a','y'),xor('d','d','a'),rotate('d',8),
            add('c','c','d'),xor('b','b','c'),rotate('b',7)]


def g_state():
    """Owner-readable equations for G, written independently of the instruction list."""
    a,b,c,d,x,y=map(var,REGISTERS)
    a=app('add32',app('add32',a,b),x)
    d=app('ror-16',app('xor32',d,a))
    c=app('add32',c,d)
    b=app('ror-12',app('xor32',b,c))
    a=app('add32',app('add32',a,b),y)
    d=app('ror-8',app('xor32',d,a))
    c=app('add32',c,d)
    b=app('ror-7',app('xor32',b,c))
    return app('state',a,b,c,d,x,y)
