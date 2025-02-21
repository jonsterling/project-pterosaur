inductive Bwd (α : Type u) : Nat → Type u where
| emp : Bwd α 0
| snoc : Bwd α n → α → Bwd α (n+1)
deriving Repr, Hashable, BEq

@[default_instance]
instance : EmptyCollection (Bwd α 0) where
  emptyCollection := .emp

infixl:60 "⬝" => Bwd.snoc

inductive Ix : Nat → Type u where
| top : Ix (n+1)
| pop : Ix n → Ix (n+1)
deriving Repr

def Ix.pred : {n : Nat} → Ix n → Option (Ix n)
| _, .top => .none
| _, .pop .top => return .top
| _, .pop i => return .pop (← pred i)

def Ix.leftmost : {n : Nat} → Ix (n+1)
| 0 => .top
| _+1 => .pop Ix.leftmost

def Bwd.proj : Bwd α n → Ix n → α
| emp, i => by contradiction
| snoc _ x, Ix.top => x
| snoc xs _, Ix.pop i => proj xs i

def Bwd.map (f : α → β) : Bwd α n → Bwd β n
| emp => emp
| snoc xs x => snoc (Bwd.map f xs) (f x)
