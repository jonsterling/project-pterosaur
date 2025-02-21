import Pterosaur.Bwd
import Pterosaur.Term
import Pterosaur.Value
import Pterosaur.Eval
import Pterosaur.Theory

def Lvl.quote : {n : Nat} → Nat → Option (Ix n)
| 0, _ => .none
| _+1, 0 => return Ix.leftmost
| _+1, ℓ+1 => do Ix.pred (← Lvl.quote ℓ)

variable (𝕋 : Theory)

mutual
  partial
  def Value.quote : Value → Term n
  | .prod name? A B =>
    let x := fresh n A
    .prod name? A.quote (B.inst 𝕋 x).quote
  | .lam name? A M =>
    let x := fresh n A.get
    .lam name? A.get.quote (M.inst 𝕋 x).quote
  | .sum locale? selfName? (methods : RecordSpec) => .sum locale? selfName? (methods.quote selfName?)
  | .obj locale? selfName? (manifest : Closure.Dict) (dict : Closure.Dict) =>
    .obj locale? selfName? (manifest.quote selfName?) (dict.quote selfName?)
  | .neu E _ => E.quote
  | .TYPE => .TYPE
  | .error msg => .error msg

  partial
  def Closure.Dict.quote (selfName? : Option String): Closure.Dict → Term.Dict (n+1) :=
    let rec loop (self : Closure.Dict) : Closure.Dict → Term.Dict (n+1)
    | [] => .nil
    | cell@⟨ℓ, impl⟩ :: rest =>
      let x := freshTranslucent n $ .obj none selfName? self []
      let implx := (impl.inst 𝕋 x).quote
      .cons ℓ implx $ loop (self ++ [cell]) rest
    loop []

  partial
  def RecordSpec.quote (selfName? : Option String) : RecordSpec → Term.ManifestDict (n+1) :=
    let rec loop (Self : RecordSpec)
    | [] => []
    | ⟨ℓ, type, manifest?⟩ :: rest =>
      let x := fresh n $ .sum none selfName? Self
      let typex := (type.inst 𝕋 x).quote
      let manifest?x := manifest?.map λ manifest => (manifest.inst 𝕋 x).quote
      ⟨ℓ, typex, manifest?x⟩ :: loop (Self ++ [⟨ℓ, type, manifest?⟩]) rest
    Term.ManifestDict.ofList ∘ loop []

  partial
  def Value.Dict.quote : Value.Dict → Term.Dict n
  | [] => .nil
  | ⟨name, impl⟩ :: (rest : Value.Dict) =>
    .cons name impl.quote rest.quote

  partial
  def SpecRefinement.quote (selfName? : Option String) (spec : RecordSpec) : Closure.Dict → Term.Dict (n+1)
  | [] => .nil
  | ⟨ℓ, impl⟩ :: rest =>
    let x := fresh n $ .sum none selfName? spec
    let implx := impl.inst 𝕋 x
    .cons ℓ implx.quote $ SpecRefinement.quote selfName? spec rest

  partial
  def Nut.quote : Nut → Term n
  | .localVar lvl =>
    match Lvl.quote lvl with
    | some ix => .localVar ix
    | none => .error s!"tried to quote de bruijn level {lvl} in context of length #{n}"
  | .globalVar name => .globalVar name

  partial
  def Spine.quote (M : Term n) : Spine len → Term n
  | .emp => M
  | .snoc frames frame => frame.quote (Spine.quote M frames)

  partial
  def Frame.quote (M : Term n) : Frame Value → Term n
  | .appTo N => .app M N.quote
  | .call name => .call M name
  | .refine selfName? (spec : RecordSpec) inst =>
    .refine M selfName? (spec.quote selfName?) $ SpecRefinement.quote selfName? spec inst

  partial
  def Neutral.quote {n : Nat} (neu : Neutral Value) : Term n :=
    let revealedNut : Option Value := do
      match neu.nut with
      | .localVar .. => none
      | .globalVar name =>
        guard $ name ∈ 𝕋.revelations
        𝕋.getValue name
    match revealedNut with
    | none => Spine.quote neu.nut.quote neu.frames
    | some V =>
      let result := Spine.plug 𝕋 V neu.frames
      result.quote
end
