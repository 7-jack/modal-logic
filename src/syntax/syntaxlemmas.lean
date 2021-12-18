
import syntax.syntax data.set.basic
local attribute [instance] classical.prop_decidable

open  Kproof


---------------------- Helper Lemmas ----------------------

-- A → A
lemma iden {Γ : ctx} {A : form} :
   Kproof Γ (A ⊃ A) :=
begin
exact mp (mp (@pl2 _ A (A ⊃ A) A) pl1) pl1
end

-- ⊤ is always provable
lemma prtrue {Γ : ctx} :  Kproof Γ ⊤ := iden


lemma weak {Γ : ctx} {A B : form} :
   Kproof Γ A →  Kproof (Γ ∪ B) A :=
begin
intro h,
induction h,
{apply ax, exact (set.mem_insert_of_mem _ h_h)},
{exact pl1},
{exact pl2},
{exact pl3},
{exact pl4},
{exact pl5},
{exact pl6},
{exact pl7},
{exact kdist},
{apply mp,
  {exact h_ih_hpq},
  {exact h_ih_hp}},
{exact nec h_ih }
end

-- We are able to prove axioms
lemma pr {Γ : ctx} {A : form} :
   Kproof (Γ ∪ A) A :=
begin
apply ax;
apply or.intro_left;
simp
end

-- The cut rule, 
lemma cut {Γ : ctx} {A B C : form} :
   Kproof Γ (A ⊃ B) →  Kproof Γ (B ⊃ C) →  Kproof Γ (A ⊃ C) :=
begin
intros h1 h2,
exact mp (mp pl2 (mp pl1 h2)) h1
end


lemma conv_deduction {Γ : ctx} {A B : form} :
   Kproof Γ (A ⊃ B) →  Kproof (Γ ∪ A) B :=
begin
intro h, 
exact mp (weak h) pr 
end

-- The following build up to double negation

lemma hs1 {Γ : ctx} {A B C : form} :
   Kproof Γ ((B ⊃ C) ⊃ ((A ⊃ B) ⊃ (A ⊃ C))) :=
begin
exact (mp (mp pl2 (mp pl1 pl2)) pl1)
end


lemma likemp {Γ : ctx} {A B : form} : 
   Kproof Γ (A ⊃ ((A ⊃ B) ⊃ B)) :=
begin
exact (mp (mp hs1 (mp pl2 iden)) pl1)
end


lemma dne {Γ : ctx} {A : form} :
 Kproof Γ ((¬¬A) ⊃ A) :=
begin
have h1 :  Kproof Γ (A ⊃ (A ⊃ A)), from pl1,
exact (cut (cut pl1 (cut pl7 pl7)) (mp likemp h1))
end


lemma dni {Γ : ctx} {A : form} :  Kproof Γ (A ⊃ ¬¬A) :=
begin
exact mp pl7 dne
end


lemma imp_if_imp_imp {Γ : ctx} {A B C : form} :  Kproof Γ (A ⊃ C) →  Kproof Γ (A ⊃ (B ⊃ C)) :=
begin
intro h1,
exact mp (mp pl2 (mp pl1 pl1)) h1
end


lemma cut1 {Γ : ctx} {A B C θ : form} :
   Kproof Γ (θ ⊃ (A ⊃ B)) →  Kproof Γ (B ⊃ C) →  Kproof Γ (θ ⊃ (A ⊃ C)) :=
begin
intros h1 h2,
exact cut h1 (mp pl2 (mp pl1 h2))
end


lemma imp_switch {Γ : ctx} {A B C : form} :  Kproof Γ (A ⊃ (B ⊃ C)) →  Kproof Γ (B ⊃ (A ⊃ C)) :=
begin
intro h1,
exact mp (mp pl2 (mp pl1 (mp pl2 h1))) pl1
end


lemma l2 {Γ : ctx} {A B C : form} :  Kproof Γ ((A ⊃ (B ⊃ C)) ⊃ (B ⊃ (A ⊃ C))) :=
begin
exact (mp (mp pl2 (cut pl2 hs1)) (mp pl1 pl1))
end


lemma hs2 {Γ : ctx} {A B C : form} :
   Kproof Γ ((A ⊃ B) ⊃ ((B ⊃ C) ⊃ (A ⊃ C))) :=
begin
exact (mp l2 hs1)
end


lemma cut2 {Γ : ctx} {A B C θ : form} :
   Kproof Γ (A ⊃ B) →  Kproof Γ (θ ⊃ (B ⊃ C)) →  Kproof Γ (θ ⊃ (A ⊃ C)) :=
begin
intros h1 h2,
exact imp_switch (cut h1 (imp_switch h2))
end


lemma double_imp {Γ : ctx} {A B : form} :
   Kproof Γ ((A ⊃ (A ⊃ B)) ⊃ (A ⊃ B)) :=
begin
exact mp pl2 (imp_switch iden)
end


lemma imp_imp_iff_imp {Γ : ctx} {θ A B : form} : 
   Kproof Γ (θ ⊃ (A ⊃ (A ⊃ B))) ↔  Kproof Γ (θ ⊃ (A ⊃ B)) :=
begin
split,
{intro h1,
exact cut h1 double_imp},
{intro h1,
exact cut h1 pl1}
end


lemma imp_shift {Γ : ctx} {θ A B C : form} : 
   Kproof Γ (θ ⊃ (A ⊃ (B ⊃ C))) ↔  Kproof Γ (θ ⊃ (B ⊃ (A ⊃ C))) :=
begin
split,
repeat {intro h1, exact cut h1 (cut2 pl1 pl2)}
end


lemma left_and_imp {Γ : ctx} {A B C : form} :
   Kproof Γ (B ⊃ ((A & B) ⊃ C)) →  Kproof Γ ((A & B) ⊃ C) :=
begin
intro h1,
exact mp double_imp (cut pl6 h1)
end


lemma and_right_imp {Γ : ctx} {A B C : form} : 
   Kproof Γ ((A & B) ⊃ C) ↔  Kproof Γ (B ⊃ (A ⊃ C)) :=
begin
split, 
{intro h1,
exact mp (cut2 pl1 pl2) (cut1 pl4 h1)},
intro h1,
exact left_and_imp (cut2 pl5 h1)
end


lemma not_and_subst {A B C : form} {Γ : ctx} : 
   Kproof Γ (A ↔ B) → ( Kproof Γ ¬(C & A) ↔  Kproof Γ ¬(C & B)) :=
begin
intro h1, split, 
{intro h2,
exact mp (mp pl3 (mp pl1 h2)) (cut dne (mp double_imp (cut2 (cut pl6 (mp pl6 h1)) 
  (cut pl5 pl4))))},
{intro h2,
exact mp (mp pl3 (mp pl1 h2)) (cut dne (mp double_imp (cut2 (cut pl6 (mp pl5 h1)) 
  (cut pl5 pl4))))},
end


lemma not_contra {Γ : ctx} {A : form} : 
   Kproof Γ ¬(A & ¬A) :=
begin
exact mp (mp pl3 (cut dne pl6)) (cut dne pl5)
end


lemma phi_and_true {Γ : ctx} {A : form} :  Kproof Γ ((A&¬⊥) ↔ A) :=
begin
exact (mp (mp pl4 pl5) (mp (imp_switch pl4) prtrue))
end


lemma imp_and_and_imp {Γ : ctx} {A B C θ : form} : 
   Kproof Γ (((A ⊃ B) & (C ⊃ θ))) →  Kproof Γ (((A & C) ⊃ (B & θ))) :=
begin
intro h,
exact (mp double_imp (cut (cut pl5 (mp pl5 h)) (cut2 (cut pl6 (mp pl6 h)) pl4)))
end


lemma not_contra_equiv_true {Γ : ctx} {A : form} : 
   Kproof Γ (¬(A & ¬A) ↔ ⊤) :=
begin
exact (mp (mp pl4 (mp pl1 prtrue)) (mp pl1 not_contra))
end


lemma contrapos {Γ : ctx} {A B : form} :
   Kproof Γ ((¬B) ⊃ (¬A)) ↔  Kproof Γ (A ⊃ B) :=
begin
split,
intro h1,
exact mp pl7 h1,
intro h1,
exact mp (cut (cut (mp hs1 dni) (mp hs2 dne)) pl7) h1,
end


lemma iff_not {Γ : ctx} {A B : form} :
   Kproof Γ (A ↔ B) →  Kproof Γ (¬B ↔ ¬A) :=
begin
intro h1,
have h2 :  Kproof Γ (A ⊃ B), from mp pl5 h1,
have h3 :  Kproof Γ (B ⊃ A), from mp pl6 h1,
rw ←contrapos at h2,
rw ←contrapos at h3,
exact (mp (mp pl4 h2) h3)
end


lemma contra_equiv_false {Γ : ctx} {A : form} : 
   Kproof Γ ((A & ¬A) ↔ ⊥) :=
begin
have h1 := iff_not not_contra_equiv_true,
exact (mp (mp pl4 (cut dni (cut (mp pl6 h1) dne))) (cut dni (cut (mp pl5 h1) dne)))
end


lemma and_switch {Γ : ctx} {A B : form} :  Kproof Γ ((A & B) ↔ (B & A)) :=
begin
exact (mp (mp pl4 (mp double_imp (cut pl5 (imp_switch (cut pl6 pl4))))) 
(mp double_imp (cut pl5 (imp_switch (cut pl6 pl4)))))
end


lemma and_commute {Γ : ctx} {A B C : form} :  Kproof Γ (((A & B) & C) ↔ (A & (B & C))) :=
begin
exact mp (mp pl4 (mp double_imp (imp_imp_iff_imp.mp 
  (cut (cut pl5 pl6) (cut2 pl6 (cut1 pl4 (imp_switch (cut (cut pl5 pl5) pl4)))))))) 
  (mp double_imp (imp_imp_iff_imp.mp (cut (cut pl6 pl5) 
  (imp_switch (cut pl5 (cut1 pl4 (cut2 (cut pl6 pl6) pl4)))))))
end


lemma imp_and_imp {Γ : ctx} {A B C : form} : 
   Kproof Γ (A ⊃ B) →  Kproof Γ ((C & A) ⊃ (C & B)) :=
begin
intros h1,
exact imp_and_and_imp (mp (mp pl4 iden) h1)
end


lemma demorgans {Γ : ctx} {A B : form} :  Kproof Γ (¬(A & B)) ↔  Kproof Γ (A ⊃ ¬B) :=
begin
split,
intro h1,
exact (and_right_imp.mp (mp (contrapos.mpr (mp pl5 and_switch)) h1)),
intro h1,
exact (mp (contrapos.mpr (mp pl5 and_switch)) (and_right_imp.mpr h1))
end


lemma explosion {Γ : ctx} {B : form} :  Kproof Γ (⊥ ⊃ B) :=
begin
apply contrapos.mp, exact (mp pl1 iden)
end


lemma exfalso {Γ : ctx} {A B : form} :  Kproof Γ ((A & ¬A) ⊃ B) :=
begin
exact cut not_contra explosion
end


lemma box_dn {Γ : ctx} {A : form} :  Kproof Γ ((¬□A) ↔ ¬(□(¬¬A))) :=
begin
exact mp (mp pl4 (contrapos.mpr (mp kdist (nec dne)))) (contrapos.mpr (mp kdist (nec dni)))
end


-- The following are known as dual formulas encode how □ ≃ ¬◇¬ and ◇ ≃ ¬□¬

lemma dual_equiv1 {Γ : ctx} {A : form} :  Kproof Γ ((□A) ↔ (¬(◇(¬A)))) :=
begin
exact mp (mp pl4 (cut (contrapos.mp (mp pl6 box_dn)) dni)) 
  (cut dne (contrapos.mp (mp pl5 box_dn)))
end


lemma dual_equiv2 {Γ : ctx} {A : form} :  Kproof Γ ((¬(□¬A)) ↔ (◇A)) :=
begin
exact mp (mp pl4 iden) iden,
end
