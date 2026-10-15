"""Declared AArch64 encoding of the six-register arithmetic fragment.

Abstract a,b,c,d,x,y map to physical W3..W8. Only unshifted 32-bit ADD,
EOR and immediate ROR (EXTR with equal source registers) are represented.
This model specifies instruction words; it does not establish Arm ISA
semantics, memory behavior, calling conventions, or a complete function.
"""
from .canon import parse
from .register_proof import REGISTERS,program,theory as register_theory
from .ground_proof import prove
from .word_literal import literal
from .equational_proof import app, var


def theory(bit_theory, g_definitions):
    t=register_theory(bit_theory)
    t[2].append(parse('(InstructionWords ((no-words ()) (instruction-word (Word32 InstructionWords))))'))
    for i in range(5):
        cases=[[var('reg-'+r),[],app('bit1' if (j+3)&(1<<i) else 'bit0')]
               for j,r in enumerate(REGISTERS)]
        t[4].append([var(f'register-bit-{i}'),parse('((r Register))'),var('Bit'),cases])

    def word(base,fields):
        bits=literal(base)[1:]
        for start,register in fields:
            for i in range(5):
                bits[start+i]=app(f'register-bit-{i}',register)
        return app('word32',*bits)

    d,a,b=map(var,('d','a','b'))
    cases=[]
    for name,base in (('add-register',0x0b000000),('xor-register',0x4a000000)):
        cases.append([var(name),[d,a,b],word(base,[(0,d),(5,a),(16,b)])])
    for n in range(32):
        cases.append([var(f'rotate-register-{n}'),[d,a],
                      word(0x13800000|(n<<10),[(0,d),(5,a),(16,a)])])
    t[4].append([var('encode-instruction'),parse('((i Instruction))'),var('Word32'),cases])
    t[4].append(parse('''(encode-program ((p Program)) InstructionWords
      ((halt () (no-words))
       (next (i tail) (instruction-word (encode-instruction i) (encode-program tail)))))'''))
    # The owner supplies the source-level G definitions separately from
    # the register instructions and encoding model.
    assert [d[0] for d in g_definitions] == ['g-first','g-second','g'], 'requires the three G definitions'
    t[4].extend(g_definitions)
    return t


def word_list(words):
    result=app('no-words')
    for word in reversed(words):
        result=app('instruction-word',literal(word),result)
    return result


def artifacts(t,instructions,words):
    """Prove the instruction list encodes exactly the supplied u32 words."""
    return prove(t,app('encode-program',program(instructions)),word_list(words))


def execution_artifacts(t):
    """run(program,s) = g(s), for every State constructor instance."""
    from .register_proof import composed_g_artifacts,g_instructions,g_state,initial_state
    from .ground_proof import Evaluation
    from .proof_library import Library
    from .canon import hash_of
    library=Library(hash_of(t))
    execution=library.include(*composed_g_artifacts(t))
    p=Evaluation(t)
    result,right=p.evaluate(app('g',initial_state()))
    assert result==g_state(), 'owner G definition differs from the proved instruction equations'
    left=p.lemma(execution,*initial_state()[1:])
    p.trans(left,p.sym(right))
    s=var('s')
    goal=[var('goal'),3,hash_of(t),[[s,var('State')]],
          app('eq',app('run',program(g_instructions()),s),app('g',s))]
    derivation=[var('induct'),s,[[var('state'),initial_state()[1:],p.steps]]]
    proof=[var('proof'),3,hash_of(goal),library.lemmas,derivation]
    return goal,proof
