
import data.set.basic semantics.semantics 
import semantics.definability syntax.syntaxlemmas
local attribute [instance] classical.prop_decidable

/-

In this file, we prove soundness for the K modal logic. 
In other words, we show that whenever there exists a proof of a formula,
that formula is logically entailed (and valid)

The classic way to prove this in modal logic is through induction on 
formulas, and that is mirrored in this proof.

-/

theorem soundness (Γ : ctx) (A : form) :  Kproof Γ A → entails Γ A :=
begin
intro h,
induction h,
{intros f v h x,
exact h h_A x h_h},
{intros f v x h2 h3 h4, 
exact h3}, 
{intros f v x h2 h3 h4 h5, 
apply h3, 
exact h5, 
apply h4, 
exact h5}, 
{intros f x v h1 h2 h3,
by_contradiction h4,
exact (h2 h4) (h3 h4)},
{intros f v x h1 h2 h3,
exact and.intro h2 h3},
{intros f v x h1 h2, 
exact h2.left},
{intros f v x h1 h2, 
exact h2.right},
{intros f v x h1 h2 h3, 
repeat {rw true_at_world at h2},
repeat {rw imp_false at h2}, 
rw not_imp_not at h2,
exact h2 h3}, 
{intros f v x h1 h2 h3 x' h4,
exact h2 x' h4 (h3 x' h4)}, 
{intros f v x h, 
exact (h_ih_hpq f v x h) (h_ih_hp f v x h)}, 
{intros f v h1 x y h2,
exact h_ih f v h1 y},
end


lemma soundnesshelper {Γ : ctx} {A : form} {C : set (frame)} : 
   Kproof Γ A → (∀ B ∈ Γ, valid_in_frame_class B C) → valid_in_frame_class A C :=
begin
intros h1 h2 f h3 v, induction h1,
{intro x, 
exact h2 h1_A h1_h f h3 v x},
{intros x h4 h5, 
exact h4},
{intros x h4 h5 h6, 
exact (h4 h6) (h5 h6)},
{intros x h3 h4, 
by_contradiction h5, 
specialize h3 h5, 
rw ←not_forces_imp at h3, 
exact h3 (h4 h5)},
{intros x h4 h5, 
exact and.intro h4 h5}, 
{intros x h4, 
exact h4.left}, 
{intros x h4, 
exact h4.right}, 
{intros x h4 h5, 
repeat {rw true_at_world at h4}, 
repeat {rw imp_false at h4},
rw not_imp_not at h4, 
exact h4 h5},
{intros x h3 h4, 
intros x' h5,
exact (h3 x' h5) (h4 x' h5)},
{intro x, 
exact h1_ih_hpq h2 x (h1_ih_hp h2 x)},
{intros x y h3, 
apply h1_ih, 
exact h2}
end
