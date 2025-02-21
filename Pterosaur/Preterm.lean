import Pterosaur.Prelude
import Pterosaur.Name

mutual
  inductive Preterm where
  | lam (name : String) (M : Preterm)
  | pi (name : String) (A : Preterm) (B : Preterm)
  | sig (spec : PrelocaleSpec)
  | refine (target : Preterm) (selfName? : Option String) (refinement : List (Name × Preterm))
  | object (selfName? : Option String) (methods : List (Name × Preterm))
  | app (func : Preterm) (arg : Preterm)
  | call (target : Preterm) (method : Name)
  | ann (term : Preterm) (type : Preterm)
  | var (name : Name)
  | hole (name : String)
  | reveal (name : Name) (scope : Preterm)
  | TYPE
  deriving Repr

  inductive PrelocaleSpecDecl where
  | require (type : Preterm)
  | splice (type : Preterm)

  structure PrelocaleSpec where
    selfName? : Option String
    decls : List (Name × PrelocaleSpecDecl)
  deriving Repr
end

abbrev Predict : Type := List (Name × Preterm)


inductive Predecl where
| locale (name : Name) (spec : PrelocaleSpec)
| define (name : Name) (type : Preterm) (term : Preterm)
| extendLocale (localeName : Name) (selfName : Option String) (name : Name) (type : Preterm) (term : Preterm)
deriving Repr

def Pretheory := List Predecl
