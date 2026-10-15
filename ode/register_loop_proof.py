"""Unbounded iteration/batching laws for the explicit register machine."""
from .canon import hash_of,parse
from .register_proof import theory as register_theory,composition_artifacts
from .proof_library import Library
from .equational_proof import Proof, app, equation, var


def theory(bit_theory):
    t=register_theory(bit_theory)
    t[4]+=parse('''(
      (double ((n Nat)) Nat ((zero () (zero)) (succ (k) (succ (succ (double k))))))
      (repeat-program ((n Nat) (p Program)) Program
        ((zero () (halt)) (succ (k) (append-program p (repeat-program k p)))))
      (iterate-program ((n Nat) (p Program) (s State)) State
        ((zero () s) (succ (k) (iterate-program k p (run p s))))))''')
    return t


def package(t,eq,base,step,library):
    goal=[var('goal'),3,hash_of(t, 'theory'),parse('((n Nat) (p Program) (s State))'),eq]
    derivation=[var('induct'),var('n'),[
        [var('zero'),[],base.steps],[var('succ'),[var('k')],step.steps]]]
    return goal,[var('proof'),3,hash_of(goal, 'goal'),library.lemmas,derivation]


def iteration_artifacts(t):
    """Repeated instruction-list execution equals tail-recursive state iteration."""
    lib=Library(hash_of(t, 'theory'));composition=lib.include(*composition_artifacts(t))
    n,p,s,k=map(var,('n','p','s','k'))
    zero=app('zero')
    base=Proof()
    a=base.cong('run',base.unfold('repeat-program',zero,p),base.refl(s))
    base.trans(a,base.unfold('run',app('halt'),s),base.sym(base.unfold('iterate-program',zero,p,s)))
    step=Proof()
    repeated=app('repeat-program',k,p)
    a=step.cong('run',step.unfold('repeat-program',app('succ',k),p),step.refl(s))
    b=step.lemma(composition,p,repeated,s)
    c=step.emit('ih',k,p,app('run',p,s))
    d=step.unfold('iterate-program',app('succ',k),p,s)
    step.trans(a,b,c,step.sym(d))
    eq=equation(app('run',app('repeat-program',n,p),s),app('iterate-program',n,p,s))
    return package(t,eq,base,step,lib)


def batching_artifacts(t):
    """Two executions per iteration equal twice as many single executions."""
    lib=Library(hash_of(t, 'theory'));composition=lib.include(*composition_artifacts(t))
    n,p,s,k=map(var,('n','p','s','k'))
    zero=app('zero');twice=app('append-program',p,p)
    base=Proof()
    a=base.cong('iterate-program',base.unfold('double',zero),base.refl(p),base.refl(s))
    base.trans(a,base.unfold('iterate-program',zero,p,s),
               base.sym(base.unfold('iterate-program',zero,twice,s)))
    step=Proof()
    once_state=app('run',p,s)
    twice_state=app('run',p,once_state)
    doubled=app('double',k)
    a=step.cong('iterate-program',step.unfold('double',app('succ',k)),step.refl(p),step.refl(s))
    b=step.unfold('iterate-program',app('succ',app('succ',doubled)),p,s)
    c=step.unfold('iterate-program',app('succ',doubled),p,once_state)
    d=step.emit('ih',k,p,twice_state)
    rhs=step.unfold('iterate-program',app('succ',k),twice,s)
    middle=step.cong('iterate-program',step.refl(k),step.refl(twice),step.lemma(composition,p,p,s))
    step.trans(a,b,c,d,step.sym(step.trans(rhs,middle)))
    eq=equation(app('iterate-program',app('double',n),p,s),app('iterate-program',n,twice,s))
    return package(t,eq,base,step,lib)
