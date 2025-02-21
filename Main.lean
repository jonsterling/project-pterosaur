import «Pterosaur»
import Pterosaur.Parser

def main : IO Unit := thy!⟦
  def Id : (A : Type) (x y : A) → Type := ?Id
  def refl : (A : Type) (x : A) → Id A x x := ?refl

  def isProp (A : Type) : Type :=
    (x y : A) → Id A x y

  def isSet (A : Type) : Type :=
    (x y : A) → isProp (Id A x y)

  locale hProp { P =>
    prf : Type,
    prf.isProp : isProp P·prf
  }

  locale Magma { A =>
    car : Type,
    car.isSet : isSet A·car,
    cmp : (x y : A·car) → A·car
  }

  locale Magma.Hom { f =>
    dom : Magma,
    cod : Magma,
    car : (x : f·dom·car) → f·cod·car,
    cmp : (x y : f·dom·car) → Id f·cod·car (f·car (f·dom·cmp x y)) (f·cod·cmp (f·car x) (f·car y))
  }

  locale Semigroup { A =>
    splice magma : Magma,
    cmp.assoc : (x y z : A·car) → Id A·car (A·cmp (A·cmp x y) z) (A·cmp x (A·cmp y z))
  }

  locale Semigroup.Hom {f =>
    dom : Semigroup,
    cod : Semigroup,
    splice magma.hom : Magma.Hom / {dom := f·dom·magma, cod := f·cod·magma}
  }

  locale CommutativeOperation {A =>
    car : Type,
    cmp : (x y : A·car) → A·car,
    cmp.commutative : (x y : A·car) → Id A·car (A·cmp x y) (A·cmp y x)
  }

  locale Monoid { A =>
    splice semigroup : Semigroup,
    unit : A·car,
    cmp.leftUnit : (x : A·car) → Id A·car (A·cmp A·unit x) x,
    cmp.rightUnit : (x : A·car) → Id A·car (A·cmp x A·unit) x
  }

  locale Monoid.Hom {f =>
    dom : Monoid,
    cod : Monoid,
    splice semigroup.hom : Semigroup.Hom / {dom := f·dom·semigroup, cod := f·cod·semigroup},
    unit : Id f·cod·car (f·car f·dom·unit) f·cod·unit
  }

  locale Predicate { P =>
    base : Type,
    mem : (x : P·base) → Type,
    mem.isProp : (x : P·base) → isProp (P·mem x)
  }

  locale Member { M =>
    pred : Predicate,
    val : M·pred·base,
    prf : M·pred·mem M·val
  }

  for P:Predicate def subtype : Type :=
    Member / {pred := P}

  for P:Predicate def subtypeIsSet : (x : isSet P·base) → isSet P·subtype :=
    ? -- TODO

  locale Subsemigroup {U =>
    base : Semigroup,
    splice predicate : Predicate / {base := U·base·car},
    cmp.closed : (x y : U·base·car) (px : U·mem x) (py : U·mem y) → U·mem (U·base·cmp x y)
  }

  locale Submonoid { U =>
    base : Monoid,
    splice subsemigroup : Subsemigroup / {base := U·base·semigroup},
    unit.closed : U·mem U·base·unit
  }

  for U:Subsemigroup def semigroup : Semigroup := { 𝒮 =>
    car := U·predicate·subtype,
    cmp x y := {foo => val := U·base·cmp x·val y·val, prf := U·cmp.closed x·val y·val x·prf y·prf},
    car.isSet := U·predicate·subtypeIsSet U·base·car.isSet,
    cmp.assoc := ?cmp.assoc
  }

  def Monoid.ofSemigroup (U:Semigroup) (M : Monoid / {car := U·car, cmp := U·cmp, car.isSet := U·car.isSet, cmp.assoc := U·cmp.assoc}) : Monoid := M

  for U:Submonoid def monoid : Monoid :=
    Monoid.ofSemigroup U·subsemigroup·semigroup {
      unit := {val := U·base·unit, prf := U·unit.closed},
      cmp.leftUnit := ?cmp.leftUnit,
      cmp.rightUnit := ?cmp.rightUnit
    }

  locale Group { G =>
    splice monoid : Monoid,
    inv : (x : G·car) → G·car,
    inv.inv : (x : G·car) → Id G·car (G·inv (G·inv x)) x
  }

  locale Subgroup { U =>
    base : Group,
    splice submonoid : Submonoid / {base := U·base·monoid},
    inv.closed : (x : U·base·car) (px : U·mem x) → U·mem (U·base·inv x)
  }

  def Group.ofMonoid (U : Monoid) (G : Group / {car := U·car, cmp := U·cmp, unit := U·unit, car.isSet := U·car.isSet, cmp.assoc := U·cmp.assoc, cmp.leftUnit := U·cmp.leftUnit, cmp.rightUnit := U·cmp.rightUnit}) : Group := G

  for U:Subgroup def group : Group :=
    Group.ofMonoid U·submonoid·monoid {
      inv x := {val := U·base·inv x·val, prf := U·inv.closed x·val x·prf},
      inv.inv := ?inv.inv
    }

  locale AbelianGroup { A =>
    splice group : Group,
    splice commutativeOperation : CommutativeOperation / {car := A·car, cmp := A·cmp}
  }

  locale Ring { A =>
    car : Type,
    car.isSet : isSet A·car,
    mul : (x y : A·car) → A·car,
    add : (x y : A·car) → A·car,
    zero : A·car,
    neg : (x : A·car) → A·car,
    one : A·car,
    dist.left : (x y z : A·car) → Id A·car (A·mul x (A·add y z)) (A·add (A·mul x y) (A·mul x z)),
    dist.right : (x y z : A·car) → Id A·car (A·mul (A·add y z) x) (A·add (A·mul y x) (A·mul z x)),
    multiplicativeMonoid : Monoid / {car := A·car, cmp := A·mul, unit := A·one, car.isSet := A·car.isSet},
    additiveGroup : AbelianGroup / {car := A·car, cmp := A·add, unit := A·zero, inv := A·neg, car.isSet := A·car.isSet}
  }
⟧

#eval main
