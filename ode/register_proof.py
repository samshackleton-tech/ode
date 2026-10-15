"""Explicit six-register arithmetic-machine semantics and reduction proofs.

This is a total abstract machine with six initialized Word32 registers,
straight-line ADD/XOR/immediate-ROR instructions, and no memory or flags.
It is not an AArch64 decoder or an ISA refinement theorem.
"""
from .canon import hash_of,parse
from .arx_proof import theory as arithmetic_theory
from .ground_proof import Evaluation
from .equational_proof import app, equation, var

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
    t[4].append(parse('''(append-program ((p Program) (q Program)) Program
        ((halt () q) (next (i tail) (next i (append-program tail q)))))'''))
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
    """G's two half equations, independent of the instruction list."""
    from .ground_proof import substitute
    first=half_state('x',16,12)
    return substitute(half_state('y',8,7),dict(zip(map(var,REGISTERS),first[1:])))


def composition_artifacts(t):
    """run(append(p,q),s) = run(q,run(p,s)), for all programs and states."""
    params=parse('((p Program) (q Program) (s State))')
    eq=parse('(eq (run (append-program p q) s) (run q (run p s)))')
    derivation=parse('''(induct p (
      (halt () (
        (unfold append-program (halt) q)
        (refl s)
        (cong run 0 1)
        (refl q)
        (unfold run (halt) s)
        (cong run 3 4)
        (sym 5)
        (trans 2 6)))
      (next (i tail) (
        (unfold append-program (next i tail) q)
        (refl s)
        (cong run 0 1)
        (unfold run (next i (append-program tail q)) s)
        (trans 2 3)
        (ih tail q (step i s))
        (trans 4 5)
        (refl q)
        (unfold run (next i tail) s)
        (cong run 7 8)
        (sym 9)
        (trans 6 10)))))''')
    goal=[var('goal'),3,hash_of(t),params,eq]
    proof=[var('proof'),3,hash_of(goal),[],derivation]
    return goal,proof


def half_state(message, first_rotation, second_rotation):
    """The equations of one G half, independent of register-step semantics."""
    assert message in ('x','y') and 0 <= first_rotation < 32 and 0 <= second_rotation < 32
    a,b,c,d,x,y=map(var,REGISTERS)
    a=app('add32',app('add32',a,b),var(message))
    d=app(f'ror-{first_rotation}',app('xor32',d,a))
    c=app('add32',c,d)
    b=app(f'ror-{second_rotation}',app('xor32',b,c))
    return app('state',a,b,c,d,x,y)


def composed_g_artifacts(t):
    """Prove G by two seven-instruction halves and the general composition law."""
    from .ground_proof import prove as prove_ground
    from .proof_library import Library
    from .equational_proof import Proof
    library=Library(hash_of(t))
    composition=library.include(*composition_artifacts(t))
    instructions=g_instructions()
    first_program,second_program=program(instructions[:7]),program(instructions[7:])
    first_state=half_state('x',16,12)
    second_state=half_state('y',8,7)
    first=library.include(*prove_execution(t,instructions[:7],first_state))
    second=library.include(*prove_execution(t,instructions[7:],second_state))
    appended=app('append-program',first_program,second_program)
    concatenation=library.include(*prove_ground(t,appended,program(instructions)))
    p=Proof()
    start=p.sym(p.cong('run',p.lemma(concatenation),p.refl(initial_state())))
    join=p.lemma(composition,first_program,second_program,initial_state())
    middle=p.cong('run',p.refl(second_program),p.lemma(first,*initial_state()[1:]))
    end=p.lemma(second,*first_state[1:])
    p.trans(start,join,middle,end)
    goal=[var('goal'),3,hash_of(t),[[var(r),var('Word32')] for r in REGISTERS],
          equation(app('run',program(instructions),initial_state()),g_state())]
    proof=[var('proof'),3,hash_of(goal),library.lemmas,[var('derive'),p.steps]]
    return goal,proof


def normalized_output(t, execution_goal, execution_proof, register):
    """Connect a State execution theorem to one normalized output equation.

    Requires an execution equation whose right side is an explicit six-word
    state of arithmetic expressions over its Word32 parameters. The supplied
    execution proof is included as a lemma and must pass kernel checking.
    Selecting an output is proof decomposition, not a partial state claim:
    each result states exactly the one register it establishes.
    """
    from .arx_proof import export_normalizer
    from .proof_library import Library
    from .proof_slice import slice_proof
    from .equational_proof import Proof
    assert register in REGISTERS, 'unknown output register'
    state=execution_goal[4][2]
    assert isinstance(state,list) and len(state)==7 and state[0]=='state', 'requires an explicit final state'
    assert all(sort=='Word32' for _,sort in execution_goal[3]), 'execution parameters must be Word32'
    expression=state[1+REGISTERS.index(register)]
    normal_goal,normal_proof=export_normalizer(t,expression)
    declared={name for name,_ in execution_goal[3]}
    assert all(name in declared for name,_ in normal_goal[3]), 'final state contains undeclared inputs'
    library=Library(hash_of(t))
    execution=library.include(execution_goal,execution_proof)
    normalization=library.include(normal_goal,normal_proof)
    p=Proof()
    projection='state-'+register
    first=p.cong(projection,p.lemma(execution,*[name for name,_ in execution_goal[3]]))
    middle=p.unfold(projection,state)
    last=p.lemma(normalization,*[name for name,_ in normal_goal[3]])
    p.trans(first,middle,last)
    goal=[var('goal'),3,hash_of(t),execution_goal[3],
          equation(app(projection,execution_goal[4][1]),normal_goal[4][2])]
    proof=[var('proof'),3,hash_of(goal),library.lemmas,[var('derive'),p.steps]]
    return goal,slice_proof(proof)
