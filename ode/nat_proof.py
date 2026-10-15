"""A proof producer outside the reliance set for natural-number addition.

It emits proofs of identity, successor, commutativity, associativity,
and exchange from the defining equations of add; then it uses those
proved lemmas to normalize sums. No kernel, evaluator, or solver import.
The kernel independently checks every inference, including all lemmas.
This is natural arithmetic, not modular-u32 arithmetic.
"""
from .canon import Sym, hash_of, parse
from .equational_proof import Normalizer, lemma_rules, app
from .proof_slice import slice_proof


def arithmetic_lemmas():
    """Closed lemmas, in dependency order; indices are used by the producer."""
    def induction(params, equation, base, step):
        return parse(f"""(lemma {params} {equation}
          (induct a ((zero () {base}) (succ (k) {step}))))""")

    return [
        induction("((a Nat))", "(eq (add a (zero)) a)",
                  "((unfold add (zero) (zero)))",
                  "((unfold add (succ k) (zero)) (ih k) (cong succ 1) (trans 0 2))"),
        induction("((a Nat) (b Nat))", "(eq (add a (succ b)) (succ (add a b)))",
                  """((unfold add (zero) (succ b))
                      (unfold add (zero) b) (cong succ 1) (sym 2) (trans 0 3))""",
                  """((unfold add (succ k) (succ b))
                      (ih k b) (cong succ 1) (trans 0 2)
                      (unfold add (succ k) b) (cong succ 4) (sym 5) (trans 3 6))"""),
        induction("((a Nat) (b Nat))", "(eq (add a b) (add b a))",
                  "((unfold add (zero) b) (lemma 0 b) (sym 1) (trans 0 2))",
                  """((unfold add (succ k) b) (ih k b) (cong succ 1) (trans 0 2)
                      (lemma 1 b k) (sym 4) (trans 3 5))"""),
        induction("((a Nat) (b Nat) (c Nat))",
                  "(eq (add (add a b) c) (add a (add b c)))",
                  """((unfold add (zero) b) (refl c) (cong add 0 1)
                      (unfold add (zero) (add b c)) (sym 3) (trans 2 4))""",
                  """((unfold add (succ k) b) (refl c) (cong add 0 1)
                      (unfold add (succ (add k b)) c) (trans 2 3)
                      (ih k b c) (cong succ 5) (trans 4 6)
                      (unfold add (succ k) (add b c)) (sym 8) (trans 7 9))"""),
        parse("""(lemma ((a Nat) (b Nat) (c Nat))
          (eq (add a (add b c)) (add b (add a c)))
          (derive ((lemma 3 a b c) (sym 0) (lemma 2 a b) (refl c)
                   (cong add 2 3) (trans 1 4) (lemma 3 b a c) (trans 5 6))))"""),
    ]


def prove(theory, parameters, left, right):
    """Propose a goal and a proof. The owner selects the actual goal.

    The producer claims equality only when flattening and sorting sums
    gives the same list, counting multiplicity. Sorting is proof search,
    not a rule: the kernel checks the derivation it produces.
    """
    lemmas=arithmetic_lemmas()
    laws=lemma_rules({'right':0,'comm':2,'assoc':3,'exchange':4})
    laws['left']=app('unfold',Sym('add'),[Sym('zero')])
    p=Normalizer('add',[Sym('zero')],laws)
    lhs,a=p.normalize(left)
    rhs,b=p.normalize(right)
    if lhs!=rhs:
        raise ValueError('the two sums have different multisets of terms')
    p.trans(a,p.sym(b))
    goal=[Sym('goal'),3,hash_of(theory),parameters,[Sym('eq'),left,right]]
    proof=[Sym('proof'),3,hash_of(goal),lemmas,[Sym('derive'),p.steps]]
    return goal,slice_proof(proof)
