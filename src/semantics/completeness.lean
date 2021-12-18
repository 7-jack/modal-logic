
import semantics.consistency syntax.soundness

local attribute [instance] classical.prop_decidable

open  Kproof

/-

In this file we prove completeness (found near the end of the file) for
K modal logic.

The classic proof goes like this utilizes a canonical model for K. In other words,
a modal model where the worlds are sets of formulas such that whenever there is 
a set Γ that is consistent, there also a exists a world for it. Furthermore, 
the accesibility relation and valuation function are defined such that truth
in a world and membership in one of the worlds are the same thing. 

The big helper functions needed are to prove Lindenbaum's lemma, which states
that a set of formulas Γ is complete iff for every formula A, we have at least 
one of A ∈ Γ or ¬A ∈ Γ. This is proved in consistency.#check

Another helper function that is important is the Truth lemma, such that whenever
a world in the canonical model satisfies a formula, that formula is in the 
world itself (because recall the worlds are sets of formulas). 

-/

namespace canonical


def canonical (Γ : ctx) [hax : sem_cons Γ] : frame := 
{ 
  W := {xΓ : ctx // max_ax_consist Γ xΓ},
  W_inhabited := 
  begin 
    have h1 := max_ax_exists Γ hax, 
    choose Γ h1 using h1, 
    exact subtype.inhabited h1,
  end,
  R := λ xΓ yΔ, ∀ A : form, □A ∈ xΓ.val → A ∈ yΔ.val
}


def val_canonical (Γ : ctx) [hax : sem_cons Γ] : nat → (canonical Γ).W → Prop :=
  λ n, λ xΓ : (canonical Γ).W, (p n) ∈ xΓ.val


lemma existence (Γ : ctx) (hax : sem_cons Γ) (xΓ : (canonical Γ).W) :
  ∀ A, ◇A ∈ xΓ.val ↔ ∃ yΔ : (canonical Γ).W, A ∈ yΔ.val ∧ (canonical Γ).R xΓ yΔ :=
begin
intro A, split,
intro h1,
let Γbox : ctx := {B : form | □B ∈ xΓ.val},
have h1 : ax_consist Γ (Γbox ∪ {A}), 
{by_contradiction h2, simp at h2,
have h3 := five Γ Γbox A h2,
cases h3 with L h3, cases h3 with h3 h4,
have h5 := cut fin_conj_boxn (mp kdist (nec h4)),
have h6 := exercise1,
have h7 : ∀ B ∈ (list.map □ L), B ∈ xΓ.1, 
intros B h8, simp at *, cases h8 with a h8,
cases h8 with h8l h8r,
subst h8r, exact h3 a h8l,
specialize h6 xΓ.2 h7 h5,
have h8 := (six Γ xΓ.1 (max_imp_ax xΓ.2)).mp xΓ.2 (¬A).box,
cases h8 with h8l h8r, simp at *,
exact absurd h1 (h8r h6)
},
have h2 := lindenbaum Γ (Γbox ∪ {A}) h1,
cases h2 with Δ h2, cases h2 with h2 h3,
let xΔ : (canonical Γ).W := ⟨Δ, h2⟩,
existsi (xΔ : (canonical Γ).W),
have h5 := set.union_subset_iff.mp h3,
cases h5, split, simp at h5_right, exact h5_right,
have h3 : ∀ A : form, □A ∈ xΓ.val → A ∈ xΔ.val,
intros B h4, apply h5_left, exact h4,
exact h3,
simp at *,
intros yΔ h1 h2,
by_contradiction h3,
have h4 := (max_notiff Γ xΓ.1 xΓ.2 (◇A)).mp h3,
have h5 := (max_dn Γ xΓ.1 xΓ.2 (□¬A)).mpr h4,
have h6 := (max_notiff Γ yΔ.1 yΔ.2 A).mpr (h2 (¬A) h5),
exact absurd h1 h6
end


lemma truth (Γ : ctx) (hax : sem_cons Γ) (xΓ : (canonical Γ).W) : 
  ∀ A, true_at_world (canonical Γ) (val_canonical Γ) xΓ A ↔ (A ∈ xΓ.val) :=
begin
intro A, induction A with n A B ih_A ih_B 
A B ih_A ih_B A ih_A generalizing xΓ,
split, intro h1, exact false.elim h1,
intro h1,
have h2 := xΓ.2,
cases h2,
specialize h2_left [⊥],
simp at *,
exact absurd not_contra (h2_left h1),
repeat {rw true_at_world, rw val_canonical},
split, intro h1, cases h1 with h1 h2,
exact max_conj_1 xΓ.2 (and.intro ((ih_A xΓ).mp h1) ((ih_B xΓ).mp h2)), 
intro h1, split,
apply (ih_A xΓ).mpr, exact max_conj_2 xΓ.2 h1,
apply (ih_B xΓ).mpr, exact max_conj_3 xΓ.2 h1,
split, 
intro h1,
apply max_imp_1 xΓ.2,
intro h2,
exact (ih_B xΓ).mp (h1 ((ih_A xΓ).mpr h2)),
intros h1 h2,
apply (ih_B xΓ).mpr,
exact max_imp_2 xΓ.2 h1 ((ih_A xΓ).mp h2),
split, intros h1, 
by_contradiction h2,
have h4 := (existence Γ hax xΓ (¬A)).mp,
have h5 := max_boxdn Γ xΓ.1 xΓ.2 A ((max_notiff Γ xΓ.1 xΓ.2 A.box).mp h2),
cases h4 h5 with xΔ h4, cases h4 with h4 h6,
have h7 := max_notiff Γ xΔ.1 xΔ.2 A,
cases h7 with h7l h7r,
exact absurd ((ih_A xΔ).mp (h1 xΔ h6)) (h7r h4),
intros h1 xΔ h2,
apply (ih_A xΔ).mpr, exact h2 A h1,
end


lemma comphelper (Γ : ctx) (A : form) (hax : sem_cons Γ) : 
  ¬  Kproof Γ A → ax_consist Γ {¬A} :=
begin
intro h1, intros L h2,
rw fin_ax_consist, induction L,
by_contradiction h3,
exact absurd (mp dne h3) (nprfalse Γ hax), 
have h4 : (∀ B ∈ L_hd::L_tl, B = ¬A) →  Kproof Γ (¬fin_conj (L_hd::L_tl)) →  Kproof Γ A, 
from fin_conj_repeat hax,
simp at *, 
cases h2 with h2 h3,
intro h6, apply h1, apply h4 h2, 
exact h3,
exact h6
end 


theorem forcesΓ (Γ : ctx) (hax : sem_cons Γ) : 
  ctx_true_in_model (canonical Γ) (val_canonical Γ) Γ :=
begin
intros A xΓ h1,
have h2 : ∀ B ∈ list.nil, B ∈ xΓ.val, 
{intros B h3, have h4 := list.ne_nil_of_length_pos (list.length_pos_of_mem h3),
simp at *, exact false.elim h4},
exact (truth Γ hax xΓ A).mpr (exercise1 xΓ.2 h2 (mp pl1 (ax h1)))
end


theorem completeness (Γ : ctx) (hax : sem_cons Γ) (A : form) : 
  entails Γ A →  Kproof Γ A :=
begin
rw ←not_imp_not, 
intro h1,
have h2 := comphelper Γ A hax h1,
have h3 := lindenbaum Γ {¬A} h2,
simp at *,
cases h3 with Γ' h3, cases h3 with h3 h4, 
rw entails, 
push_neg,
let f := canonical, use f Γ,
let v := val_canonical, use v Γ,
let xΓ' : (f Γ).W := ⟨Γ', h3⟩,
split, 
exact forcesΓ Γ hax,
use xΓ',
have h5 := truth Γ hax xΓ' ¬A,
cases h5 with h5 h6,
have h7 := not_forces_imp (f Γ) (v Γ) xΓ' A,
cases h7 with h7 h8, apply h8, apply h6, exact h4
end

end canonical
