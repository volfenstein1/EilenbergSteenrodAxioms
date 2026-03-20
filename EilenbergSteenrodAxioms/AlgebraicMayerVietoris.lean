/-
Copyright (c) 2026 Wolfgang Schamltz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wolfgang Schmaltz
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Abelian.Refinements

@[expose] public section

open CategoryTheory ShortComplex Limits

namespace AlgebraicMayerVietoris

structure AlgMayerVietorisPreInput (V : Type*) [Category V] [Abelian V] where
  /- Objects -/
  {A B C D E F A' B' C' D' E' F' : V}
  /- Horizontal Morphisms -/
  (mor_AB : A ⟶ B)
  (mor_BC : B ⟶ C)
  (mor_CD : C ⟶ D)
  (mor_DE : D ⟶ E)
  (mor_EF : E ⟶ F)
  (mor_A'B' : A' ⟶ B')
  (mor_B'C' : B' ⟶ C')
  (mor_C'D' : C' ⟶ D')
  (mor_D'E' : D' ⟶ E')
  (mor_E'F' : E' ⟶ F')
  /- Vertical Morphisms -/
  mor_AA' : A ⟶ A'
  mor_BB' : B ⟶ B'
  mor_CC' : C ⟶ C'
  mor_DD' : D ⟶ D'
  mor_EE' : E ⟶ E'
  mor_FF' : F ⟶ F'
  /- The vertical morphism A ⟶ A' and D ⟶ D' are isomorphisms. -/
  excision_iso_AA' : IsIso mor_AA'
  excision_iso_DD' : IsIso mor_DD'
  /- Commutativity Conditions -/
  comm_AB : mor_AB ≫ mor_BB' = mor_AA' ≫ mor_A'B'
  comm_BC : mor_BC ≫ mor_CC' = mor_BB' ≫ mor_B'C'
  comm_CD : mor_CD ≫ mor_DD' = mor_CC' ≫ mor_C'D'
  comm_DE : mor_DE ≫ mor_EE' = mor_DD' ≫ mor_D'E'
  comm_EF : mor_EF ≫ mor_FF' = mor_EE' ≫ mor_E'F'
  /- Im ⊆ Ker -/
  zero_ABC : mor_AB ≫ mor_BC = 0
  zero_BCD : mor_BC ≫ mor_CD = 0
  zero_CDE : mor_CD ≫ mor_DE = 0
  zero_DEF : mor_DE ≫ mor_EF = 0
  zero_A'B'C' : mor_A'B' ≫ mor_B'C' = 0
  zero_B'C'D' : mor_B'C' ≫ mor_C'D' = 0
  zero_C'D'E' : mor_C'D' ≫ mor_D'E' = 0
  zero_D'E'F' : mor_D'E' ≫ mor_E'F' = 0

/- Short Complexes -/
namespace AlgMayerVietorisPreInput

variable {V : Type*} [Category V] [Abelian V]
variable (Y : AlgMayerVietorisPreInput V)

def S_ABC : ShortComplex V := ShortComplex.mk Y.mor_AB Y.mor_BC Y.zero_ABC
def S_BCD : ShortComplex V := ShortComplex.mk Y.mor_BC Y.mor_CD Y.zero_BCD
def S_CDE : ShortComplex V := ShortComplex.mk Y.mor_CD Y.mor_DE Y.zero_CDE
def S_DEF : ShortComplex V := ShortComplex.mk Y.mor_DE Y.mor_EF Y.zero_DEF

def S_A'B'C' : ShortComplex V := ShortComplex.mk Y.mor_A'B' Y.mor_B'C' Y.zero_A'B'C'
def S_B'C'D' : ShortComplex V := ShortComplex.mk Y.mor_B'C' Y.mor_C'D' Y.zero_B'C'D'
def S_C'D'E' : ShortComplex V := ShortComplex.mk Y.mor_C'D' Y.mor_D'E' Y.zero_C'D'E'
def S_D'E'F' : ShortComplex V := ShortComplex.mk Y.mor_D'E' Y.mor_E'F' Y.zero_D'E'F'

end AlgMayerVietorisPreInput

structure AlgMayerVietorisInput (V : Type*) [Category V] [Abelian V] extends AlgMayerVietorisPreInput V where
  /- Exactness -/
  exact_ABC : Exact (toAlgMayerVietorisPreInput.S_ABC)
  exact_BCD : Exact (toAlgMayerVietorisPreInput.S_BCD)
  exact_CDE : Exact (toAlgMayerVietorisPreInput.S_CDE)
  exact_DEF : Exact (toAlgMayerVietorisPreInput.S_DEF)
  exact_A'B'C' : Exact (toAlgMayerVietorisPreInput.S_A'B'C')
  exact_B'C'D' : Exact (toAlgMayerVietorisPreInput.S_B'C'D')
  exact_C'D'E' : Exact (toAlgMayerVietorisPreInput.S_C'D'E')
  exact_D'E'F' : Exact (toAlgMayerVietorisPreInput.S_D'E'F')

noncomputable section
variable {V : Type*} [Category V] [Abelian V]
variable (Z : AlgMayerVietorisInput V)

/-- The map A ⟶ A' ⊞ B constructed using the universal property of the product -/
def α : Z.B ⟶ Z.B' ⊞ Z.C :=
  biprod.lift Z.mor_BB' (-Z.mor_BC)

/-- The map A' ⊞ B ⟶ B' constructed using the universal property of the coproduct -/
def β : Z.B' ⊞ Z.C ⟶ Z.C' :=
  biprod.desc Z.mor_B'C' Z.mor_CC'

/- The boundary map B' ⟶ D via B' ⟶ C' ⟵ C ⟶ D -/
def Δ : Z.C' ⟶ Z.E :=
  haveI : IsIso Z.mor_DD' := Z.excision_iso_DD'
  Z.mor_C'D' ≫ inv Z.mor_DD' ≫ Z.mor_DE

/-- The map D ⟶ D' ⊞ E constructed using the universal property of the product -/
def γ : Z.E ⟶ Z.E' ⊞ Z.F :=
  biprod.lift Z.mor_EE' (-Z.mor_EF)

lemma αβ_zero {Z : AlgMayerVietorisInput V} : (α Z) ≫ (β Z) = 0 := by
  unfold α β
  rw [biprod.lift_desc, Preadditive.neg_comp, Z.comm_BC, add_neg_cancel]

lemma βΔ_zero {Z : AlgMayerVietorisInput V} : (β Z) ≫ (Δ Z) = 0 := by
  unfold β Δ
  haveI := Z.excision_iso_DD'
  apply biprod.hom_ext'
  · -- Component 1: Path through B'
    rw [biprod.inl_desc_assoc, comp_zero]
    slice_lhs 1 2 =>
      rw [Z.zero_B'C'D']
    rw [zero_comp, zero_comp]
  · -- Component 2: Path through C
    rw [biprod.inr_desc_assoc]
    slice_lhs 1 2 =>
      rw [← Z.comm_CD]
    slice_lhs 2 3 =>
      rw [IsIso.hom_inv_id]
    rw [Category.id_comp, comp_zero] 
    rw [Z.zero_CDE]

lemma Δγ_zero {Z : AlgMayerVietorisInput V} : (Δ Z) ≫ (γ Z) = 0 := by
  unfold Δ γ
  haveI := Z.excision_iso_DD'
  apply biprod.hom_ext
  · -- Component 1: Projection to E'
    rw [Category.assoc, biprod.lift_fst]
    rw [Category.assoc, Category.assoc, Z.comm_DE]
    rw [IsIso.inv_hom_id_assoc]
    rw [Z.zero_C'D'E', zero_comp]
  · -- Component 2: Projection to F
    rw [Category.assoc, biprod.lift_snd, zero_comp]
    rw [Preadditive.comp_neg, Category.assoc, neg_eq_zero]
    slice_lhs 3 4 =>
      rw [Z.zero_DEF]
    rw [comp_zero, comp_zero]

/- Define the short complexes -/
def S_αβ := ShortComplex.mk (α Z) (β Z) (by exact αβ_zero)
def S_βΔ := ShortComplex.mk (β Z) (Δ Z) (by exact βΔ_zero) 
def S_Δγ := ShortComplex.mk (Δ Z) (γ Z) (by exact Δγ_zero)

lemma αβ_exact {Z : AlgMayerVietorisInput V} : (S_αβ Z).Exact := by
  /- Rewrite exactness in terms of the abstract condition of refinements. -/
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  unfold S_αβ
  /- (b'c : B' ⊞ C) and suppose that β (b'c) = 0 -/
  simp only [exists_prop]
  intro B'C₀ b'c b'c_ker
  /- Split b'c into components b' : B'C₀ ⟶ B' and c : B'C₀ ⟶ C -/
  let b' := b'c ≫ biprod.fst
  let c := b'c ≫ biprod.snd
  /- We have: -/
  /-    b'c ≫ β = 0  -/
  /-    b' ≫ mor_B'C' + c ≫ mor_CC' = 0. -/
  have h_eq : b' ≫ Z.mor_B'C' + c ≫ Z.mor_CC' = 0 := by
    unfold b' c
    unfold β at b'c_ker
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add]
    rw [← biprod.desc_eq]
    exact b'c_ker
  /- We have: -/
  /-   b' ≫ mor_B'C' + c ≫ mor_CC' = 0 -/
  /-   b' ≫ mor_B'C' ≫ mor_C'D' + c ≫ mor_CC' ≫ mor_C'D' = 0 -/
  /-   c ≫ mor_CC' ≫ mor_C'D' = 0 -/
  have h_c_ker1 : c ≫ Z.mor_CC' ≫ Z.mor_C'D' = 0 := by
    apply_fun (· ≫ Z.mor_C'D') at h_eq
    rw [Preadditive.add_comp] at h_eq
    rw [Category.assoc] at h_eq
    rw [Z.zero_B'C'D'] at h_eq
    rw [comp_zero, zero_add, zero_comp, Category.assoc] at h_eq
    exact h_eq
  /- We have: -/
  /-   c ≫ mor_CC' ≫ mor_C'D' = 0 -/
  /-   c ≫ mor_CD ≫ mor_DD' = 0   (since the diagram commutes) -/
  /-   c ≫ mor_CD = 0             (since mor_DD' is an isomorphism) -/
  have h_c_ker2 : c ≫ Z.mor_CD = 0 := by
    unfold c
    rw [← Z.comm_CD] at h_c_ker1
    haveI := Z.excision_iso_DD' 
    apply_fun (· ≫ inv (Z.mor_DD')) at h_c_ker1
    rw [Category.assoc, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id, zero_comp, ← Category.assoc] at h_c_ker1
    exact h_c_ker1

  /- We use exactness of the short complex B ⟶ C ⟶ D applied to c ≫ mor_CD = 0. -/
  have h_exact_at_C := (Z.exact_BCD)
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at h_exact_at_C
  obtain ⟨B₀, πb, hπb_cover, b₀, hb₀_lift⟩ := h_exact_at_C c h_c_ker2
  change B₀ ⟶ Z.B at b₀
  change πb ≫ c = b₀ ≫ Z.mor_BC at hb₀_lift
  clear h_eq h_c_ker1 h_c_ker2 h_exact_at_C

  /- Introduce a new arrow b'_Δ : B₀ ⟶ B' := b₀ ≫ mor_BB' + πb₀ ≫ b' -/
  let b'_Δ : B₀ ⟶ Z.B' := b₀ ≫ Z.mor_BB' + πb ≫ b' 

  /- We show that: b'_Δ ≫ mor_B'C' = 0. -/
  have b'_Δ_ker : b'_Δ ≫ Z.mor_B'C' = 0 := by
    unfold b'_Δ
    rw [Preadditive.add_comp, Category.assoc]
    rw [← Z.comm_BC, ← Category.assoc]
    rw [← hb₀_lift]
    unfold b' c
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]
    rw [← Preadditive.comp_add, ← Preadditive.comp_add]
    rw [add_comm]
    rw [← biprod.desc_eq]
    unfold β at b'c_ker
    rw [b'c_ker, comp_zero]
  
  /- We use exactness of the short complex A' ⟶ B' ⟶ C' applied to b'_Δ ≫ mor_B'C' = 0. -/
  have h_exact_at_B' := (Z.exact_A'B'C')
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at h_exact_at_B'
  obtain ⟨A'₀, πa', hπa'_cover, a', ha'_lift⟩ := h_exact_at_B' b'_Δ b'_Δ_ker
  change A'₀ ⟶ Z.A' at a'
  change πa' ≫ b'_Δ = a' ≫ Z.mor_A'B' at ha'_lift
  clear h_exact_at_B'

  /- Introduce an arrow b₁ : A'₀ ⟶ B := a' ≫ inv mor_AA' ≫ mor_AB -/
  haveI :=  Z.excision_iso_AA'
  let b₁ : A'₀ ⟶ Z.B := a' ≫ inv (Z.mor_AA') ≫ Z.mor_AB

  /- We have a lift: b₁ ≫ mor_BB' = πa' ≫ b'_Δ -/
  have h_b1 : b₁ ≫ Z.mor_BB' = πa' ≫ b'_Δ := by
    unfold b₁
    simp only [Category.assoc]
    rw [Z.comm_AB]
    rw [IsIso.inv_hom_id_assoc]
    rw [ha'_lift]

  /- Introduce an arrow b : A'₀ ⟶ B := b₁ - πa' ≫ b₀ -/
  let b : A'₀ ⟶ Z.B := b₁ - πa' ≫ b₀

  /- We then have:                                                -/
  /-                     (b₁ - πa' ≫ b₀) ≫ mor_BB' = b ≫ mor_BB'  -/
  /-             b₁ ≫ mor_BB' - πa' ≫ b₀ ≫ mor_BB' =              -/
  /-               πa' ≫ b'_Δ - πa' ≫ b₀ ≫ mor_BB' =              -/
  /-                   πa' ≫ (b'_Δ - b₀ ≫ mor_BB') =              -/
  /- πa' ≫ (b₀ ≫ mor_BB' + πb ≫ b' - b₀ ≫ mor_BB') =              -/
  /-                                 πa' ≫ πb ≫ b' =              -/
  have h_bb' : πa' ≫ πb ≫ b'= b ≫ Z.mor_BB' := by
    unfold b b₁
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc]
    rw [Z.comm_AB]
    rw [IsIso.inv_hom_id_assoc]
    rw [← ha'_lift]
    unfold b'_Δ
    simp

  /-                                  - (b₁ - πa' ≫ b₀) ≫ mor_BC = -b ≫ mor_BC -/
  /-                           - b₁ ≫ mor_BC - πa' ≫ b₀ ≫ mor_BC =             -/
  /- - (a' ≫ inv mor_AA' ≫ mor_AB ≫ mor_BC - πa' ≫ b₀ ≫ mor_BC)  =             -/
  /-                                           πa' ≫ b₀ ≫ mor_BC =             -/
  /-                                                πa' ≫ πb ≫ c =             -/
  have h_bc : πa' ≫ πb ≫ c = -b ≫ Z.mor_BC := by
    unfold b b₁
    simp
    rw [hb₀_lift]
    rw [Z.zero_ABC]
    simp

  use A'₀, πa' ≫ πb
  constructor
  · apply epi_comp
  · use b
    unfold α 
    apply biprod.hom_ext
    /- πa' ≫ πb ≫ b' = b ≫ mor_BB' -/
    · simp only [Category.assoc, biprod.lift_fst]
      exact h_bb'
    /- πa' ≫ πb ≫ c = (b₁ - (πa' ≫ b₀)) ≫ mor_BC -/
    · simp only [Category.assoc, biprod.lift_snd, Preadditive.comp_neg]
      exact h_bc

lemma βΔ_exact {Z : AlgMayerVietorisInput V} : (S_βΔ Z).Exact := by
  /- Rewrite exactness in terms of the abstract condition of refinements. -/
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  unfold S_βΔ
  simp only [exists_prop]
  intro C'₀ c'₀ c'₀_ker
  unfold Δ at c'₀_ker
  haveI :=  Z.excision_iso_DD'
  let d := c'₀ ≫ Z.mor_C'D' ≫ inv (Z.mor_DD')
  have d_ker_morDE : d ≫ Z.mor_DE = 0 := by
    unfold d
    rw [Category.assoc, Category.assoc]
    exact c'₀_ker

  /- We use exactness of the short complex C ⟶ D ⟶ E applied to d ≫ mor_DE = 0. -/
  /- Hence we get an arrow c : C₀ ⟶ C such that πc ≫ d = c ≫ mor_CD -/
  have h_exact_at_D := (Z.exact_CDE)
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at h_exact_at_D
  obtain ⟨C₀, πc, hπc_cover, c, hc_lift⟩ := h_exact_at_D d d_ker_morDE
  change C₀ ⟶ Z.C at c
  change πc ≫ d = c ≫ Z.mor_CD at hc_lift
  clear h_exact_at_D

  /- Introduce an arrow c'₁ : C₀ ⟶ C' := πc ≫ c'₀ - c ≫ mor_CC' -/
  let c'₁ : C₀ ⟶ Z.C' := πc ≫ c'₀ - c ≫ (Z.mor_CC') 
  /- The arrow c'₁ is in the kernel of mor_C'D':                                         -/
  /- c'₁ ≫ mor_C'D' = (πc ≫ c'₀ - c ≫ mor_CC') ≫ mor_C'D'                                -/
  /-                = πc ≫ c'₀ ≫ mor_C'D' - c ≫ mor_CC' ≫ mor_C'D'                       -/
  /-                = πc ≫ c'₀ ≫ mor_C'D' - c ≫ mor_CD ≫ mor_DD'                         -/
  /-                = πc ≫ c'₀ ≫ mor_C'D' - πc ≫ d ≫ mor_DD'                             -/
  /-                = πc ≫ c'₀ ≫ mor_C'D' - πc ≫ c'₀ ≫ mor_C'D' ≫ inv mor_DD' ≫ mor_DD'  -/
  /-                = πc ≫ c'₀ ≫ mor_C'D' - πc ≫ c'₀ ≫ mor_C'D'                          -/
  /-                = 0                                                                  -/
  have c'₁_ker_morC'D' : c'₁ ≫ Z.mor_C'D' = 0 := by 
    unfold c'₁ 
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc]
    rw [← Z.comm_CD]
    rw [sub_eq_zero]
    slice_rhs 1 2 =>
      rw [← hc_lift]
    unfold d
    simp

  /- We use exactness of the short complex B' ⟶ C' ⟶ D' applied to c'₁ ≫ mor_C'D' = 0. -/
  /- Hence we get an arrow b' : B'₀ ⟶ B' such that πb' ≫ c'₁ = b' ≫ mor_B'C'. -/
  have h_exact_at_C' := (Z.exact_B'C'D')
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at h_exact_at_C'
  obtain ⟨B'₀, πb', hπb'_cover, b', hb'_lift⟩ := h_exact_at_C' c'₁ c'₁_ker_morC'D'
  change B'₀ ⟶ Z.B' at b'
  change πb' ≫ c'₁ = b' ≫ Z.mor_B'C' at hb'_lift
  clear h_exact_at_C'

  /- We then have:                                                                   -/
  /-               πb' ≫ c'₁ + πb' ≫ c ≫ mor_CC' = b' ≫ mor_B'C' + πb' ≫ c ≫ mor_CC' -/
  /-                   πb' ≫ (c'₁ + c ≫ mor_CC') =                                   -/
  /- πb' ≫ (πc ≫ c' - c ≫ mor_CC' + c ≫ mor_CC') =                                   -/
  /-                              πb' ≫ πc ≫ c'₀ =                                   -/
  have hc : πb' ≫ πc ≫ c'₀ = b' ≫ Z.mor_B'C' + πb' ≫ c ≫ Z.mor_CC' := by
    rw [← hb'_lift]
    rw [← Preadditive.comp_add]
    unfold c'₁
    simp

  use B'₀, πb' ≫ πc
  constructor
  · apply epi_comp
  · use biprod.lift b' (πb' ≫ c)
    unfold β
    rw [biprod.lift_desc, Category.assoc, Category.assoc]
    exact hc


lemma Δγ_exact {Z : AlgMayerVietorisInput V} : (S_Δγ Z).Exact := by
  /- Rewrite exactness in terms of the abstract condition of refinements. -/
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  unfold S_Δγ
  simp only [exists_prop]
  intro E₀ e e_ker

  /- We split e ≫ γ = 0 into e ≫ mor_EE' = 0 and e ≫ mor_EF = 0. -/
  have e_ker_morEE' : e ≫ Z.mor_EE' = 0 := by 
    unfold γ at e_ker
    apply_fun (fun x => x ≫ biprod.fst) at e_ker
    rw [Category.assoc, biprod.lift_fst, zero_comp] at e_ker
    exact e_ker
  have e_ker_morEF : e ≫ Z.mor_EF = 0 := by
    unfold γ at e_ker
    apply_fun (fun x => x ≫ biprod.snd) at e_ker
    rw [Category.assoc, biprod.lift_snd, zero_comp] at e_ker
    rw [Preadditive.comp_neg, neg_eq_zero] at e_ker
    exact e_ker

  /- We use exactness of the short complex D ⟶ E ⟶ F applied to e ≫ mor_EF = 0. -/
  /- Hence we get an arrow d: D₀ ⟶ D such that πd ≫ e = d ≫ mor_DE.             -/
  have h_exact_at_E := (Z.exact_DEF)
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at h_exact_at_E
  obtain ⟨D₀, πd, hπd_cover, d, hd_lift⟩ := h_exact_at_E e e_ker_morEF
  change D₀ ⟶ Z.D at d
  change πd ≫ e = d ≫ Z.mor_DE at hd_lift
  clear h_exact_at_E

  /- Introduce an arrow d' : D₀ ⟶ D' := d ≫ mor_DD'. -/
  let d' : D₀ ⟶ Z.D' := d ≫ Z.mor_DD'
  /- The arrow d' is in the kernel of mor_D'E': -/
  have h_d' : d' ≫ Z.mor_D'E' = 0 := by
    unfold d'
    rw [Category.assoc, ← Z.comm_DE]
    rw [← Category.assoc, ← hd_lift, Category.assoc]
    rw [e_ker_morEE', comp_zero]

  /- We use exactness of the short complex C' ⟶ D' ⟶ E' applied to d' ≫ mor_D'E' = 0. -/
  /- Hence we get an arrow c': C'₀ ⟶ C' such that πc' ≫ d' = c' ≫ mor_C'D'.           -/
  have h_exact_at_D' := (Z.exact_C'D'E')
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at h_exact_at_D'
  obtain ⟨C'₀, πc', hπc'_cover, c', hc'_lift⟩ := h_exact_at_D' d' h_d'
  change C'₀ ⟶ Z.C' at c'
  change πc' ≫ d' = c' ≫ Z.mor_C'D' at hc'_lift  
  clear h_exact_at_D'

  /- We then have:                                       -/
  /-     c' ≫ mor_C'D' ≫ inv (mor_DD') ≫ mor_DE = c' ≫ Δ -/
  /-          πc' ≫ d' ≫ inv (mor_DD') ≫ mor_DE =        -/
  /- πc' ≫ d ≫ mor_DD' ≫ inv (mor_DD') ≫ mor_DE =        -/
  /-                           πc' ≫ d ≫ mor_DE =        -/
  /-                               πc' ≫ πd ≫ e =        -/
  haveI :=  Z.excision_iso_DD'
  have hc' : πc' ≫ πd ≫ e = c' ≫ Z.mor_C'D' ≫ inv (Z.mor_DD') ≫ Z.mor_DE := by
    slice_rhs 1 2 =>
      rw [← hc'_lift]
    unfold d'
    slice_rhs 3 4 =>
      rw [IsIso.hom_inv_id]
    rw [Category.id_comp]
    rw [hd_lift]

  use C'₀, πc' ≫ πd  
  constructor
  · apply epi_comp
  · use c'
    rw [Category.assoc]
    exact hc'
end
end AlgebraicMayerVietoris
