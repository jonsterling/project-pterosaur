import Pterosaur.LocalEnv

abbrev Local (m : Type → Type) (O : Nat → Type) n :=
  LocalEnv n
  → m (O n)

abbrev Con (I : Type) (m : Type → Type) (O : Nat → Type) n :=
  Local (ReaderT I m) O n

abbrev ElabM := StateT Theory (ExceptT String IO)

abbrev ValueSynthesiser m := Local m λ _ => Defined
abbrev TermSynthesiser m := Local m TypedTerm
abbrev ValueChecker m := Con Value m λ _ => Value
abbrev TermChecker m := Con Value m Term

abbrev RecordSpecExtender m := Con (Value × RecordSpec) m (λ _ => RecordSpec)
abbrev RecordSpecRefiner m := Con RecordSpec m (λ _ => RecordSpec)

-- Produces a dictionary of manifest fields and a dictionary of primary fields
abbrev ObjectDictChecker m :=
  Con RecordSpec m λ n =>
  Term.Dict (n+1) × Term.Dict (n+1)

inductive CoercionResult α where
| identity : Thunk α → CoercionResult α
| expansion : α → CoercionResult α
deriving Nonempty

def CoercionResult.get : CoercionResult α → α
| identity x => x.get
| expansion x => x

def CoercionResult.map (f : α → β) : CoercionResult α → CoercionResult β
| .identity x => .identity $ x.map f
| .expansion x => .expansion $ f x

def CoercionResult.bind (f : α → CoercionResult β) : CoercionResult α → CoercionResult β
| .identity x => f x.get
| .expansion x => .expansion (f x).get

abbrev CoerceTerm m := Con (Value × Value × Value) m (CoercionResult ∘ Term)

instance [Monad m] : Nonempty (CoerceTerm m n) :=
  .intro λ _ _ =>
  return .expansion $ .obj none none .nil .nil


variable [Monad m] [MonadState Theory m] [MonadExcept String m]

partial
def assertUnusedName (name : Name) : m Unit := do
  let 𝕋 ← get
  if name ∈ 𝕋.globals then
    throw s!"Attempted to shadow global name `{name}`"

partial
def assertUnusedLocaleName (name : Name) : m Unit := do
  let 𝕋 ← get
  if name ∈ 𝕋.locales then
    throw s!"Attempted to shadow global locale name `{name}`"

def convert (Γ : LocalEnv n) (U V : Value) : m Unit := do
  try Value.convert (← get) n U V catch
  | error => do
    let 𝕋 ← get
    let M : Term n := U.whnf.quote 𝕋
    let N : Term n := V.whnf.quote 𝕋
    throw s!"When converting {M.format Γ.names 0} and {N.format Γ.names 0}, encountered: {error}"
