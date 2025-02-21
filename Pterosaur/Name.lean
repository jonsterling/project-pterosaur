import Pterosaur.Prelude
import Pterosaur.Bwd

inductive Name.Component where
| user (str : String)
| machine (str : String)
deriving Hashable, BEq

instance : Repr Name.Component where
  reprPrec
  | .user str, _ => str
  | .machine str, _ => f!"#{str}"

structure Name where
  {len : Nat}
  cpts : Bwd Name.Component (len+1)
deriving Hashable, BEq

def Name.reprPrecComponents : {len : Nat} → Bwd Name.Component (len+1) → Nat → Std.Format
| 0, Bwd.emp ⬝ x, _ => reprPrec x 0
| _+1, name ⬝ x, _ => f!"{Name.reprPrecComponents name 0}/{reprPrec x 0}"

instance : Repr Name where
  reprPrec name := Name.reprPrecComponents name.cpts

def Name.ofString (str : String) : Name :=
  {cpts := {} ⬝ .user str }

instance : Coe String Name where
  coe := Name.ofString

instance : ToString Name where
  toString x := reprStr x

def Name.sub (name : Name) (cpt : Name.Component) :=
  {name with len := _, cpts := name.cpts ⬝ cpt}
