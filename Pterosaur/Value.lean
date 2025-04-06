import Pterosaur.Bwd
import Pterosaur.Term
import Std.Data.HashMap

inductive Nut : Type where
| localVar : Nat → Nut
| globalVar : Name → Nut
deriving Repr

structure Closure (α : Type u) : Type u where
  {len : Nat}
  locals : Bwd α len
  inside : Term (len + 1)
deriving Repr

def Closure.const (V : α) : Closure α :=
  ⟨{}⬝V, .localVar (.pop .top)⟩

structure ManifestCell (α : Type u) : Type u where
  type : Closure α
  manifest? : Option (Closure α)
deriving Repr

inductive Frame (α : Type u) : Type u where
| appTo (arg : α)
| call (ℓ : Name)
| refine (selfName? : Option String) (spec : List (Name × ManifestCell α)) (inst : List (Name × Closure α))
deriving Repr

structure Neutral (α : Type u) : Type u where
  nut : Nut
  {len : Nat}
  frames : Bwd (Frame α) len
deriving Repr


instance : Nonempty (Closure α) := .intro ⟨ {}, .obj none none .nil .nil ⟩

instance [Repr α] : Repr (Thunk α) where
  reprPrec th n := reprPrec th.get n

inductive Boundary (α : Type u) : Type u where
| abstract (type : Thunk α)
| translucent (value: Thunk α)
deriving Repr

mutual
  inductive Value : Type where
  | neu : Neutral Value → Boundary Value → Value
  | funTp (name? : Option String) (dom : Value) (cod : Closure Value)
  | rcdTp (locale? : Option Name) (selfName? : Option String) (tele : List (Name × ManifestCell Value))
  | lam (name? : Option String) (dom : Thunk Value) (body : Closure Value)
  | obj (locale? : Option Name) (selfName? : Option String) (manifest dict : List (Name × Closure Value))
  | TYPE
  | error (msg : String)
  deriving Repr, Inhabited
end

abbrev Value.Dict := List (Name × Value)
abbrev Closure.Dict := List (Name × Closure Value)
abbrev RecordSpec := List (Name × ManifestCell Value)

abbrev Spine len := Bwd (Frame Value) len

def Value.whnf : Value → Value
| .neu _ (.translucent V) => Value.whnf V.get
| V => V

def Value.destructFunTp : Value → Option (Option String × Value × Closure Value)
| .neu _ (.translucent V) => V.get.destructFunTp
| .funTp name? A B => return ⟨ name?, A, B ⟩
| _ => none

def Value.destructRcdTp : Value → Option (Option Name × Option String × RecordSpec)
| .neu _ (.translucent V) => V.get.destructRcdTp
| .rcdTp locale? selfName? spec => some ⟨locale?, selfName?, spec⟩
| _ => none

def Value.destructTYPE : Value → Option Unit
| .neu _ (.translucent V) => V.get.destructTYPE
| .TYPE => return ()
| _ => none

def fresh (n : Nat) (type : Value) : Value :=
  .neu ⟨.localVar n, {}⟩ (.abstract type)

def freshTranslucent (n : Nat) (value : Value) : Value :=
  .neu ⟨.localVar n, {}⟩ (.translucent value)

def Closure.Dict.toRecordSpec (Φ : Closure.Dict) : RecordSpec :=
  Φ.map λ ⟨ℓ, A⟩ => ⟨ℓ, ⟨A, none⟩⟩

def Value.Dict.toClosureDict (dict : Value.Dict) : Closure.Dict :=
  dict.map λ ⟨ℓ,x⟩ => ⟨ℓ, .const x⟩

def Value.struct (localeName? : Option Name) (mfst self : Value.Dict) : Value :=
  Value.obj localeName? none mfst.toClosureDict self.toClosureDict

structure PurifiedRecordSpec where
  methods : Closure.Dict
  partialManifest : Closure.Dict

def RecordSpec.purify : RecordSpec → PurifiedRecordSpec :=
  let rec loop (OldSelf : RecordSpec) (purified : PurifiedRecordSpec) : RecordSpec → PurifiedRecordSpec
  | [] => purified
  | ⟨ℓ, cell@⟨A,M?⟩⟩ :: rest =>
    let manifestObj := Value.obj none none purified.partialManifest []
    let tpOldSelf := Value.rcdTp none none OldSelf
    let update clo : Closure Value :=
      ⟨{} ⬝ Value.lam none tpOldSelf clo ⬝ manifestObj,
      let methods :=
        OldSelf.map λ ⟨ℓ,_⟩ =>
        let ix : Ix 3 :=
          match purified.partialManifest.lookup ℓ with
          | none => .top
          | some _ => .pop .top
        ⟨ℓ, .call (.localVar $ .pop ix) ℓ⟩
      .app (.localVar (.pop (.pop .top))) $ .obj none none (.ofList methods) .nil⟩
    match M? with
    | none => loop (OldSelf ++ [⟨ℓ, cell⟩]) ({purified with methods := purified.methods ++ [⟨ℓ, update A⟩]}) rest
    | some M => loop (OldSelf ++ [⟨ℓ, cell⟩]) {purified with partialManifest := purified.partialManifest ++ [⟨ℓ, update M⟩]} rest

  loop [] {partialManifest := {}, methods := {}}




def Term.ManifestDict.close (γ : Bwd Value n) : Term.ManifestDict (n+1) → RecordSpec
| .nil => []
| .consAbstract name type rest =>
  ⟨name, ⟨γ, type⟩, none⟩ :: rest.close γ
| .consManifest name type manifest rest =>
  ⟨name, ⟨γ, type⟩, some ⟨γ, manifest⟩⟩ :: rest.close γ

def Term.Dict.close (γ : Bwd Value n) : Term.Dict (n+1) → List (Name × Closure Value)
| .nil => []
| .cons name term rest => ⟨name, ⟨γ, term⟩⟩ :: rest.close γ

def Frame.plugNeutral (neu : Neutral Value) (frm : Frame Value) : Neutral Value :=
  {neu with
    len := neu.len + 1,
    frames := neu.frames ⬝ frm}
