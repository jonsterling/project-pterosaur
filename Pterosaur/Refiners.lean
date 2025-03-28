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
import Pterosaur.Refiners.Product
import Pterosaur.Refiners.Sum
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
    let locale := {selfName?, spec, extensions := {}}
    assertUnusedLocaleName name
    assertUnusedName name
    modify $ Theory.insertLocale name locale
    let defn ← Connective.Sum.formation.locale name (.refine none []) ({} : LocalEnv 0)
    modify $ Theory.insertGlobal name $ .translucent defn
    let type := Term.globalVar name
    let foo := Term.sum none "self" (@spec.quote (← get) 0 "self")
    IO.println f!"Declared locale {name} equivalent to: {Std.Format.line}{Std.Format.nest 1 (foo.format {} 0)}\n"
    return {value := type.eval (← get) {}, type := defn.type}

  def extendLocale (localeName : Name) (name : Name) (selfName? : Option String) (tacA : TermChecker m 1) (tacM : TermChecker m 1) : m Unit := do
    let 𝕋 ← get
    match 𝕋.locales[localeName]? with
    | none => throw s!"Could not extend nonexistent locale `{localeName}`"
    | some locale =>
      let Self := Value.sum localeName selfName? locale.spec
      let self := fresh 0 Self
      let Γ := LocalEnv.empty.ext selfName? Self self
      let tmA ← tacA Γ .TYPE
      let valA := tmA.eval (← get) Γ.values
      let tmM ← tacM Γ valA
      let extension := {
        type := ⟨{}, tmA⟩,
        impl := ⟨{}, tmM⟩
      }
      let locale := {
        locale with
          extensions := locale.extensions.insert name extension
      }
      MonadState.set {𝕋 with locales := 𝕋.locales.insert localeName locale}
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
    | .prod .. => Connective.Product.coercion autoCoerceTerm autoCoerceTerm
    | .sum .. => Connective.Sum.coercion autoCoerceTerm
    | _ => .shift
end Tactic
