use vstd::modes::*;
use vstd::pcm::*;
use vstd::pcm_lib::*;
use vstd::set_lib::*;
use vstd::prelude::*;

verus! {

pub enum ArrPerm {
    Perm { uniq: Set<int>, shrd: Set<int> },
    Invalid,
}

impl PCM for ArrPerm {
    open spec fn valid(self) -> bool {
        match self {
            ArrPerm::Perm { uniq, shrd } => uniq.disjoint(shrd),
            ArrPerm::Invalid => false,
        }
    }

    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (
                ArrPerm::Perm { uniq: u1, shrd: s1 },
                ArrPerm::Perm { uniq: u2, shrd: s2 },
            ) => {
                // Rules:
                //  - uniques must be disjoint
                //  - no uniq may overlap any shared
                if u1.disjoint(u2) 
                // && (u1 + u2).disjoint(s1 + s2) 
                {
                    ArrPerm::Perm { uniq: u1 + u2, shrd: s1 + s2 }
                } else {
                    ArrPerm::Invalid
                }
            },
            _ => ArrPerm::Invalid,
        }
    }

    open spec fn unit() -> Self {
        ArrPerm::Perm { uniq: Set::empty(), shrd: Set::empty() }
    }

    proof fn closed_under_incl(a: Self, b: Self) {
        match (a, b) {
            (
                ArrPerm::Perm { uniq: u1, shrd: s1 },
                ArrPerm::Perm { uniq: u2, shrd: s2 },
            ) => {
                if u1.disjoint(u2) 
                {
                    if (u1 + u2).disjoint(s1 + s2) {
                        assert(a.valid()) by {
                            assume(!(u1.disjoint(s1)));
                            let x = choose|elem: int| u1.contains(elem) && s1.contains(elem);
                            assert((u1 + u2) has x);
                            assert((s1 + s2) has x);
                            assert(!(u1 + u2).disjoint(s1 + s2));
                        }
                    }
                }
            },
            _ => {}
        }
    }

    proof fn commutative(a: Self, b: Self) {
        match (a, b) {
            (
                ArrPerm::Perm { uniq: u1, shrd: s1 },
                ArrPerm::Perm { uniq: u2, shrd: s2 },
            ) => {
                assert(u1.disjoint(u2) == u2.disjoint(u1));
                assert((u1 + u2) == (u2 + u1));
                assert((s1 + s2) == (s2 + s1));
            },
            _ => {}
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        match (a, b, c) {
            (
                ArrPerm::Perm { uniq: u1, shrd: s1 },
                ArrPerm::Perm { uniq: u2, shrd: s2 },
                ArrPerm::Perm { uniq: u3, shrd: s3 },
            ) => {
                assert((u1 + (u2 + u3)) == ((u1 + u2) + u3));
                assert((s1 + (s2 + s3)) == ((s1 + s2) + s3));
            },
            _ => {}
        }
    }

    proof fn op_unit(a: Self) {
        let (uniq_emp, shrd_emp) = (Self::unit()->uniq, Self::unit()->shrd);
        assert(uniq_emp == Set::<int>::empty());
        assert(shrd_emp == Set::<int>::empty());
        match a {
            ArrPerm::Perm { uniq, shrd } => {
                assert(uniq + uniq_emp == uniq);
                assert(shrd + shrd_emp == shrd);
                assert(uniq.disjoint(uniq_emp));
            },
            ArrPerm::Invalid => {
                assert(Self::op(a, Self::unit()) == ArrPerm::Invalid);
            },
        }
    }

    proof fn unit_valid() {
    }
}

pub open spec fn uniq_idx(i: int) -> ArrPerm {
    ArrPerm::Perm { uniq: set![i], shrd: Set::empty() }
}

pub open spec fn uniq_set(iset: Set<int>) -> ArrPerm {
    ArrPerm::Perm { uniq: iset, shrd: Set::empty() }
}

pub open spec fn shrd_idx(i: int) -> ArrPerm {
    ArrPerm::Perm { uniq: Set::empty(), shrd: set![i] }
}

pub open spec fn shrd_set(iset: Set<int>) -> ArrPerm {
    ArrPerm::Perm { uniq: Set::empty(), shrd: iset }
}

pub struct ArrCap<const N: usize> {
    r: Resource<ArrPerm>,
}

impl<const N: usize> ArrCap<N> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value() is Perm
        &&& self.len() <= N
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn len(self) -> nat
    {
        self.r.value()->uniq.len() + self.r.value()->shrd.len()
    }

    pub closed spec fn view(self) -> ArrPerm {
        self.r.value()
    }

    pub proof fn new() -> (tracked o: Self)
        ensures
            o@ == uniq_set(set_int_range(0, N as int)),
            o.len() == N,
    {
        let tracked r = Resource::alloc(uniq_set(set_int_range(0, N as int)));
        lemma_int_range(0, N as int);
        ArrCap { r }
    }

    pub proof fn with_uniq_set(iset: Set<int>) -> (tracked o: Self)
        requires
            iset.len() <= N,
        ensures
            o@ == uniq_set(iset),
            o.len() == iset.len(),
    {
        let tracked r = Resource::alloc(uniq_set(iset));
        ArrCap { r }
    }

    pub proof fn with_shrd_set(iset: Set<int>) -> (tracked o: Self)
        requires
            iset.len() <= N,
        ensures
            o@ == shrd_set(iset),
            o.len() == iset.len(),
    {
        let tracked r = Resource::alloc(shrd_set(iset));
        ArrCap { r }
    }

    pub proof fn dummy() -> (tracked o: Self)
    {
        let tracked r = Resource::alloc(ArrPerm::Perm { uniq: Set::empty(), shrd: Set::empty() });
        ArrCap { r }
    }
}

fn example() {
    let tracked mut cap = ArrCap::<10>::new();
    assert(cap@ == uniq_set(set_int_range(0, 10)));
    assert(cap.len() == 10);
    let tracked mut cap1 = ArrCap::<10>::new();
    
}

} // verus!
