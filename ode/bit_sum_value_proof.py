"""Numeric correctness of ripple-carry addition for arbitrary paired bit lists.

Pairing the two input bits in each column gives equal-width inputs by
construction. The output keeps the final carry. Numeric values use Nat;
no machine-integer evaluator or modular arithmetic axiom is involved.
"""
from .canon import hash_of,parse
from .adder_value_proof import theory as column_theory,artifacts as column_artifacts
from .nat_proof import prove as prove_natural
from .ground_proof import Evaluation
from .proof_library import Library
from .proof_slice import slice_proof
from .equational_proof import Proof,app,equation,var


def theory(bit_theory,nat_theory):
    t=column_theory(bit_theory,nat_theory)
    t[2].append(next(d for d in bit_theory[2] if d[0]=='Bits'))
    t[2].append(parse('(Columns ((no-columns ()) (column (Bit Bit Columns))))'))
    t[4]+=parse('''(
      (left-bits ((columns Columns)) Bits
        ((no-columns () (empty)) (column (a b tail) (bit a (left-bits tail)))))
      (right-bits ((columns Columns)) Bits
        ((no-columns () (empty)) (column (a b tail) (bit b (right-bits tail)))))
      (add-columns ((columns Columns) (c Bit)) Bits
        ((no-columns () (bit c (empty)))
         (column (a b tail)
           (bit (xor-bit (xor-bit a b) c) (add-columns tail (carry-bit a b c))))))
      (bits-value ((bits Bits)) Nat
        ((empty () (zero))
         (bit (a tail) (add (bit-value a) (add (bits-value tail) (bits-value tail)))))))''')
    return t


def artifacts(t):
    library=Library(hash_of(t,'theory'))
    column_rule=library.include(*column_artifacts(t))
    S,C,A,B,a,b,c=map(var,('S','C','A','B','a','b','c'))
    add=lambda x,y:app('add',x,y)
    twice=lambda x:add(x,x)
    pre_left=add(S,twice(add(A,add(B,C))))
    pre_right=add(add(S,twice(C)),add(twice(A),twice(B)))
    before=library.include(*prove_natural(t,[[v,var('Nat')] for v in (S,C,A,B)],pre_left,pre_right))
    post_left=add(add(a,add(b,c)),add(twice(A),twice(B)))
    post_right=add(add(a,twice(A)),add(add(b,twice(B)),c))
    after=library.include(*prove_natural(t,[[v,var('Nat')] for v in (a,b,c,A,B)],post_left,post_right))
    columns,tail=var('columns'),var('tail')
    value=lambda bits:app('bits-value',bits)
    bit_value=lambda bit:app('bit-value',bit)

    def claim(xs):
        return equation(value(app('add-columns',xs,c)),
                        add(value(app('left-bits',xs)),add(value(app('right-bits',xs)),bit_value(c))))

    base=Evaluation(t)
    left,left_proof=base.evaluate(claim(app('no-columns'))[1])
    right,right_proof=base.evaluate(claim(app('no-columns'))[2])
    zero_rule=library.include(*prove_natural(t,[[c,var('Bit')]],left,right))
    base.trans(left_proof,base.lemma(zero_rule,c),base.sym(right_proof))

    step=Proof()
    xs=app('column',a,b,tail)
    carry=app('carry-bit',a,b,c)
    summed=app('xor-bit',app('xor-bit',a,b),c)
    remaining=app('add-columns',tail,carry)
    first=step.cong('bits-value',step.unfold('add-columns',xs,c))
    second=step.unfold('bits-value',app('bit',summed,remaining))
    ih=step.emit('ih',tail,carry)
    third=step.cong('add',step.refl(bit_value(summed)),step.cong('add',ih,ih))
    left=step.trans(first,second,third)
    av,bv=value(app('left-bits',tail)),value(app('right-bits',tail))
    regroup=step.lemma(before,bit_value(summed),bit_value(carry),av,bv)
    column=step.cong('add',step.lemma(column_rule,a,b,c),step.refl(add(twice(av),twice(bv))))
    reorder=step.lemma(after,bit_value(a),bit_value(b),bit_value(c),av,bv)

    def projection(function,head):
        one=step.cong('bits-value',step.unfold(function,xs))
        two=step.unfold('bits-value',app('bit',head,app(function,tail)))
        return step.trans(one,two)

    rhs=step.cong('add',projection('left-bits',a),
                  step.cong('add',projection('right-bits',b),step.refl(bit_value(c))))
    step.trans(left,regroup,column,reorder,step.sym(rhs))
    goal=[var('goal'),3,hash_of(t,'theory'),[[columns,var('Columns')],[c,var('Bit')]],claim(columns)]
    derivation=[var('induct'),columns,[[var('no-columns'),[],base.steps],
                                      [var('column'),[a,b,tail],step.steps]]]
    proof=[var('proof'),3,hash_of(goal,'goal'),library.lemmas,derivation]
    return goal,slice_proof(proof)
