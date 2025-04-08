import Pterosaur.Bwd
import Pterosaur.Term
import Pterosaur.Value
import Pterosaur.Eval
import Pterosaur.Quote
import Pterosaur.Conv
import Pterosaur.Theory
import Pterosaur.LocalEnv
import Pterosaur.RefinerTypes
import Pterosaur.Refiners.Structural
import Pterosaur.Refiners.RecordSpecRefiner
import Pterosaur.Refiners.RecordSpecExtender
import Pterosaur.Refiners.ObjectDictChecker
import Pterosaur.Refiners.Function
import Pterosaur.Refiners.Record
import Pterosaur.Refiners.Universe
import Std.Data.HashMap

variable [Monad m] [MonadState Theory m] [MonadExcept String m]

namespace Kernel

  def define (name : Name) (tacA : ValueChecker m 0) (tacM : ValueChecker m 0) : m Defined := do
    let mut 𝕋 ← get
    let A ← tacA {} .TYPE
    let M ← tacM {} A
    assertUnusedName name
    modify $ Theory.insertGlobal name $ .translucent {value := M, type := A}
    𝕋 ← get
    let term := Term.globalVar name
    return {value := term.eval 𝕋 {}, type := A}

  def declareLocale (name : Name) (selfName? : Option String) (tacTele : RecordSpecExtender ElabM 0) : ElabM Defined := do
    let spec ← tacTele {} ⟨.TYPE, []⟩
    let locale := {selfName?, spec}
    assertUnusedLocaleName name
    assertUnusedName name
    modify $ Theory.insertLocale name locale
    let defn ← localeFormation name (.refine none []) ({} : LocalEnv 0)
    modify $ Theory.insertGlobal name $ .translucent defn
    let type := Term.globalVar name
    let foo := Term.rcdTp none "self" (@spec.quote (← get) 0 "self")
    IO.println f!"Declared locale {name} equivalent to: {Std.Format.line}{Std.Format.nest 1 (foo.format {} 0)}\n"
    return {value := type.eval (← get) {}, type := defn.type}

  partial
  def insertLocaleExtension (localeName : Name) (name : Name) (ext : LocaleExtension) : m Unit := do
    let rec loop (seen : Std.HashSet Name) (localeName : Name) (ext : LocaleExtension) : m Unit := do
      let 𝕋 ← get

      if localeName ∈ seen then
        throw s!"Detected loop during locale extension"

      match 𝕋.locales[localeName]? with
      | none => throw s!"Could not extend nonexistent locale `{localeName}`"
      | some localeSpec => do
        let Self := Value.rcdTp localeName none localeSpec.spec

        match localeSpec.extensions[name]? with
        | some ext' =>
          let x := fresh 0 Self
          let typex0 := ext.type.inst 𝕋 x
          let typex1 := ext'.type.inst 𝕋 x
          let Γ : LocalEnv 1 := LocalEnv.empty.ext none Self x
          convert Γ typex0 typex1
          let implx0 := ext.impl.inst 𝕋 x
          let implx1 := ext'.impl.inst 𝕋 x
          convert Γ implx0 implx1
        | none => pure ();

        let updatedSpec := {localeSpec with extensions := localeSpec.extensions.insert name ext}
        MonadState.set {𝕋 with locales := 𝕋.locales.insert localeName updatedSpec}
        for ⟨importingLocale, coercion⟩ in localeSpec.importedBy do
          loop (seen.insert localeName) importingLocale {
            type := sequenceClosure coercion $ .lam none Self ext.type,
            impl := sequenceClosure coercion $ .lam none Self ext.impl
          }

    loop {} localeName ext


  def extendLocale (localeName : Name) (name : Name) (selfName? : Option String) (tacA : TermChecker m 1) (tacM : TermChecker m 1) : m Unit := do
    let 𝕋 ← get
    match 𝕋.locales[localeName]? with
    | none => throw s!"Could not extend nonexistent locale `{localeName}`"
    | some locale =>
      let Self := Value.rcdTp localeName selfName? locale.spec
      let self := fresh 0 Self
      let Γ := LocalEnv.empty.ext selfName? Self self
      let tmA ← tacA Γ .TYPE
      let valA := tmA.eval (← get) Γ.values
      let tmM ← tacM Γ valA
      insertLocaleExtension localeName name {
        type := ⟨{}, tmA⟩,
        impl := ⟨{}, tmM⟩
      }

end Kernel

namespace Tactic
  def withGoal (tac : Value → TermChecker m n) : TermChecker m n :=
    λ Γ type =>
    tac type Γ type

  def withTopHyp (tac : Defined → Local m' O (n+1)) : Local m' O (n+1) :=
    λ Δ@⟨_⬝A, _⬝x, _⟩ =>
    tac {type := A, value := x} Δ

  partial
  def withCoercionGoalType (tac : Value → CoerceTerm m n) : CoerceTerm m n :=
    fun Γ params =>
    tac params.snd.snd Γ params

  partial
  def autoCoerceTerm {n : Nat} : CoerceTerm m n :=
    withCoercionGoalType λ type =>
    match type.whnf with
    | .funTp .. => funCoercion autoCoerceTerm autoCoerceTerm
    | .rcdTp .. => recordCoercion autoCoerceTerm
    | _ => .shift
end Tactic
