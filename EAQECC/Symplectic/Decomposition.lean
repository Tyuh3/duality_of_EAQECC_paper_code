import EAQECC.Symplectic.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.LatticeIntervals

/-!
辛子空间的分解与标准辛基。分别提取根空间、用于辅助补偿的非退化部分，
以及辛对偶中用于构造逻辑算子的非退化部分。
-/

namespace Quantum
namespace BinarySymplecticSubspace

/-- 根空间分解。把子空间分成辛根空间与一个非退化补空间；
后续证明分解存在，并在类型 [m,c]ₛ 下确定补空间维数为 2c。
-/
structure RadicalDecomposition {n : ℕ}
    (S : BinarySymplecticSubspace n) where
  nondegeneratePart : BinarySymplecticSubspace n
  disjoint_radical : Disjoint (radical S) nondegeneratePart
  radical_sup_nondegeneratePart : radical S ⊔ nondegeneratePart = S

theorem radicalDecomposition_nonempty
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    Nonempty (RadicalDecomposition S) := by
  let Rsub : Submodule (ZMod 2) S := (radical S).comap S.subtype
  obtain ⟨Esub, hCompl⟩ := Rsub.exists_isCompl
  let E : BinarySymplecticSubspace n := Esub.map S.subtype
  have hMapped : IsCompl (S.mapIic Rsub) (S.mapIic Esub) :=
    S.mapIic.isCompl_iff.mp hCompl
  have hWithin := (Set.Iic.isCompl_iff).mp hMapped
  have hRadicalLe : radical S ≤ S := inf_le_left
  have hMapRadical :
      (S.mapIic Rsub : BinarySymplecticSubspace n) = radical S := by
    change Rsub.map S.subtype = radical S
    rw [show Rsub = (radical S).comap S.subtype from rfl,
      Submodule.map_comap_subtype, inf_of_le_right hRadicalLe]
  refine ⟨⟨E, ?_, ?_⟩⟩
  · change Disjoint (radical S) (Esub.map S.subtype)
    rw [← hMapRadical]
    exact hWithin.1
  · change radical S ⊔ Esub.map S.subtype = S
    rw [← hMapRadical]
    exact hWithin.2

noncomputable def radicalDecomposition
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    RadicalDecomposition S :=
  Classical.choice (radicalDecomposition_nonempty S)

namespace RadicalDecomposition

def radicalWithin
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (_D : RadicalDecomposition S) : Submodule (ZMod 2) S :=
  (radical S).comap S.subtype

def nondegeneratePartWithin
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) : Submodule (ZMod 2) S :=
  D.nondegeneratePart.comap S.subtype

theorem nondegeneratePart_le
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) : D.nondegeneratePart ≤ S := by
  intro x hx
  rw [← D.radical_sup_nondegeneratePart]
  exact Submodule.mem_sup_right hx

theorem radicalWithin_isCompl_nondegeneratePartWithin
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) :
    IsCompl D.radicalWithin D.nondegeneratePartWithin := by
  have hRadicalLe : radical S ≤ S := inf_le_left
  apply S.mapIic.isCompl_iff.mpr
  apply Set.Iic.isCompl_iff.mpr
  constructor
  · simpa [radicalWithin, nondegeneratePartWithin,
      Submodule.map_comap_subtype, inf_of_le_right hRadicalLe,
      D.nondegeneratePart_le] using
        D.disjoint_radical
  · simpa [radicalWithin, nondegeneratePartWithin,
      Submodule.map_comap_subtype, inf_of_le_right hRadicalLe,
      D.nondegeneratePart_le] using
        D.radical_sup_nondegeneratePart

theorem nondegeneratePart_isNondegenerate
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) :
    ((binarySymplecticBilinForm n).restrict D.nondegeneratePart).Nondegenerate := by
  rw [restrictedBilinForm_nondegenerate_iff_radical_eq_bot]
  rw [radical, eq_bot_iff]
  intro v hv
  have hvE : v ∈ D.nondegeneratePart := hv.1
  have hvOrthE :
      v ∈ NQubitPauliGroupElement.sympOrthogonal D.nondegeneratePart := hv.2
  have hvS : v ∈ S := D.nondegeneratePart_le hvE
  have hvOrthR :
      v ∈ NQubitPauliGroupElement.sympOrthogonal (radical S) := by
    intro r hr
    rw [← binarySymplecticBilinForm_apply,
      (binarySymplecticBilinForm_isSymm n).eq,
      binarySymplecticBilinForm_apply]
    exact hr.2 v hvS
  have hvOrthSup :
      v ∈ NQubitPauliGroupElement.sympOrthogonal
        (radical S ⊔ D.nondegeneratePart) := by
    intro w hw
    rcases Submodule.mem_sup.mp hw with ⟨r, hr, e, he, rfl⟩
    rw [NQubitPauliOperator.symplecticBilinear_add_right,
      hvOrthR r hr, hvOrthE e he, zero_add]
  have hvRadical : v ∈ radical S := by
    refine ⟨hvS, ?_⟩
    rw [← D.radical_sup_nondegeneratePart]
    exact hvOrthSup
  exact D.disjoint_radical.le_bot ⟨hvRadical, hvE⟩

theorem nondegeneratePart_finrank_eq_two_mul_of_hasType
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    Module.finrank (ZMod 2) D.nondegeneratePart = 2 * c := by
  have hDimension := Submodule.finrank_sup_add_finrank_inf_eq
    (radical S) D.nondegeneratePart
  rw [D.radical_sup_nondegeneratePart, D.disjoint_radical.eq_bot] at hDimension
  simp at hDimension
  have hS := hType.1
  have hRadical := radicalFinrank_add_two_mul_eq_of_hasType hType
  omega

end RadicalDecomposition

/-- 逻辑部分的分解。将 S 的根空间从辛对偶中分离，
余下的非退化部分用于构造逻辑算子；在码参数条件下其维数为 2k。
-/
structure LogicalDecomposition {n : ℕ}
    (S : BinarySymplecticSubspace n) where
  logicalPart : BinarySymplecticSubspace n
  disjoint_radical : Disjoint (radical S) logicalPart
  radical_sup_logicalPart :
    radical S ⊔ logicalPart = NQubitPauliGroupElement.sympOrthogonal S

theorem logicalDecomposition_nonempty
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    Nonempty (LogicalDecomposition S) := by
  let D := radicalDecomposition
    (NQubitPauliGroupElement.sympOrthogonal S)
  refine ⟨⟨D.nondegeneratePart, ?_, ?_⟩⟩
  · simpa only [radical_sympOrthogonal] using D.disjoint_radical
  · simpa only [radical_sympOrthogonal] using
      D.radical_sup_nondegeneratePart

noncomputable def logicalDecomposition
    {n : ℕ} (S : BinarySymplecticSubspace n) :
    LogicalDecomposition S :=
  Classical.choice (logicalDecomposition_nonempty S)

namespace LogicalDecomposition

def toRadicalDecomposition
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (D : LogicalDecomposition S) :
    RadicalDecomposition (NQubitPauliGroupElement.sympOrthogonal S) where
  nondegeneratePart := D.logicalPart
  disjoint_radical := by
    simpa only [radical_sympOrthogonal] using D.disjoint_radical
  radical_sup_nondegeneratePart := by
    simpa only [radical_sympOrthogonal] using D.radical_sup_logicalPart

theorem logicalPart_le_symplecticDual
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (D : LogicalDecomposition S) :
    D.logicalPart ≤ NQubitPauliGroupElement.sympOrthogonal S :=
  D.toRadicalDecomposition.nondegeneratePart_le

theorem logicalPart_isNondegenerate
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (D : LogicalDecomposition S) :
    ((binarySymplecticBilinForm n).restrict D.logicalPart).Nondegenerate :=
  D.toRadicalDecomposition.nondegeneratePart_isNondegenerate

theorem logicalPart_finrank_eq_two_mul_of_symplecticDual_hasType
    {n m' c' : ℕ} {S : BinarySymplecticSubspace n}
    (D : LogicalDecomposition S)
    (hType : BinarySymplecticSubspace.HasType
      (NQubitPauliGroupElement.sympOrthogonal S) m' c') :
    Module.finrank (ZMod 2) D.logicalPart = 2 * c' :=
  D.toRadicalDecomposition.nondegeneratePart_finrank_eq_two_mul_of_hasType
    hType

theorem logicalPart_finrank_eq_two_mul_logicalDimension
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (D : LogicalDecomposition A.stabilizerSpace) :
    Module.finrank (ZMod 2) D.logicalPart = 2 * k := by
  have hDimension :=
    D.logicalPart_finrank_eq_two_mul_of_symplecticDual_hasType
      A.symplecticDual_hasType
  have hParameter := A.parameter_eq
  omega

end LogicalDecomposition
end BinarySymplecticSubspace
end Quantum

namespace Quantum

open LinearMap

/-- 成对辛基。将基向量分成两组，同组内辛内积为零，异组间按索引配对。
-/
structure SymplecticPairBasis
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (c : ℕ) where
  basis : Module.Basis (Fin c ⊕ Fin c) (ZMod 2) V
  left_left : ∀ i j : Fin c,
    B (basis (Sum.inl i)) (basis (Sum.inl j)) = 0
  right_right : ∀ i j : Fin c,
    B (basis (Sum.inr i)) (basis (Sum.inr j)) = 0
  left_right : ∀ i j : Fin c,
    B (basis (Sum.inl i)) (basis (Sum.inr j)) = if i = j then 1 else 0

namespace SymplecticPairBasis

noncomputable def toStandardCoordinates
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} {c : ℕ}
    (P : SymplecticPairBasis B c) :
    V ≃ₗ[ZMod 2] BinarySymplecticVector c :=
  P.basis.equivFun.trans
    (LinearEquiv.piCongrLeft (ZMod 2)
      (fun _ : Fin (c + c) => ZMod 2) finSumFinEquiv)

@[simp]
theorem toStandardCoordinates_basis_inl
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} {c : ℕ}
    (P : SymplecticPairBasis B c) (i : Fin c) :
    P.toStandardCoordinates (P.basis (Sum.inl i)) =
      Pi.single (Fin.castAdd c i) 1 := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · by_cases hij : i = j
    · subst j
      simp [toStandardCoordinates, LinearEquiv.piCongrLeft,
        LinearEquiv.piCongrLeft',
        finSumFinEquiv_symm_apply_castAdd]
    · have hji : j ≠ i := Ne.symm hij
      simp [toStandardCoordinates, LinearEquiv.piCongrLeft,
        LinearEquiv.piCongrLeft', finSumFinEquiv_symm_apply_castAdd, hji]
  · have hBlocks : Fin.natAdd c j ≠ Fin.castAdd c i := by
      intro h
      have hval := congrArg Fin.val h
      simp [Fin.castAdd] at hval
      omega
    simp [toStandardCoordinates, LinearEquiv.piCongrLeft,
      LinearEquiv.piCongrLeft', finSumFinEquiv_symm_apply_natAdd, hBlocks,
      -Fin.natAdd_eq_addNat]

@[simp]
theorem toStandardCoordinates_basis_inr
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} {c : ℕ}
    (P : SymplecticPairBasis B c) (i : Fin c) :
    P.toStandardCoordinates (P.basis (Sum.inr i)) =
      Pi.single (Fin.natAdd c i) 1 := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have hBlocks : Fin.castAdd c j ≠ Fin.natAdd c i := by
      intro h
      have hval := congrArg Fin.val h
      simp [Fin.castAdd] at hval
      omega
    simp [toStandardCoordinates, LinearEquiv.piCongrLeft,
      LinearEquiv.piCongrLeft', finSumFinEquiv_symm_apply_castAdd, hBlocks,
      -Fin.natAdd_eq_addNat]
  · by_cases hij : i = j
    · subst j
      simp [toStandardCoordinates, LinearEquiv.piCongrLeft,
        LinearEquiv.piCongrLeft',
        finSumFinEquiv_symm_apply_natAdd, -Fin.natAdd_eq_addNat]
    · have hji : j ≠ i := Ne.symm hij
      simp [toStandardCoordinates, LinearEquiv.piCongrLeft,
        LinearEquiv.piCongrLeft', finSumFinEquiv_symm_apply_natAdd, hji,
        -Fin.natAdd_eq_addNat]

/- 以下为成对辛基的归纳构造准备索引分解，并证明非退化交替形式存在这种基。
-/
private def succIndexEquiv (c : ℕ) :
    (Fin 2 ⊕ (Fin c ⊕ Fin c)) ≃ (Fin (c + 1) ⊕ Fin (c + 1)) where
  toFun
    | Sum.inl i => Fin.cases (Sum.inl 0) (fun _ => Sum.inr 0) i
    | Sum.inr (Sum.inl i) => Sum.inl i.succ
    | Sum.inr (Sum.inr i) => Sum.inr i.succ
  invFun
    | Sum.inl i => Fin.cases (Sum.inl 0) (fun j => Sum.inr (Sum.inl j)) i
    | Sum.inr i => Fin.cases (Sum.inl 1) (fun j => Sum.inr (Sum.inr j)) i
  left_inv i := by
    rcases i with i | i
    · fin_cases i <;> rfl
    · rcases i with i | i <;> rfl
  right_inv i := by
    rcases i with i | i <;> refine Fin.cases ?_ (fun _ => rfl) i <;> rfl

@[simp]
private theorem succIndexEquiv_symm_inl_zero (c : ℕ) :
    (succIndexEquiv c).symm (Sum.inl (0 : Fin (c + 1))) =
      Sum.inl (0 : Fin 2) := rfl

@[simp]
private theorem succIndexEquiv_symm_inr_zero (c : ℕ) :
    (succIndexEquiv c).symm (Sum.inr (0 : Fin (c + 1))) =
      Sum.inl (1 : Fin 2) := rfl

@[simp]
private theorem succIndexEquiv_symm_inl_succ (c : ℕ) (i : Fin c) :
    (succIndexEquiv c).symm (Sum.inl i.succ) =
      Sum.inr (Sum.inl i) := rfl

@[simp]
private theorem succIndexEquiv_symm_inr_succ (c : ℕ) (i : Fin c) :
    (succIndexEquiv c).symm (Sum.inr i.succ) =
      Sum.inr (Sum.inr i) := rfl

private theorem zmod_two_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
  apply ZMod.val_injective 2
  rw [ZMod.val_one 2]
  have hval : a.val ≠ 0 := by
    intro hzero
    exact ha ((ZMod.val_eq_zero a).mp hzero)
  have hlt := a.val_lt
  omega

theorem nonempty_of_nondegenerate
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hAlt : B.IsAlt) (hSymm : B.IsSymm) (hNondegenerate : B.Nondegenerate)
    (c : ℕ) (hDimension : Module.finrank (ZMod 2) V = 2 * c) :
    Nonempty (SymplecticPairBasis B c) := by
  induction c generalizing V with
  | zero =>
      have hZero : Module.finrank (ZMod 2) V = 0 := by
        simpa using hDimension
      letI : Subsingleton V := Module.finrank_zero_iff.mp hZero
      refine ⟨{
        basis := Module.Basis.empty V
        left_left := ?_
        right_right := ?_
        left_right := ?_ }⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ c ih =>
      have hPositive : 0 < Module.finrank (ZMod 2) V := by
        rw [hDimension]
        omega
      letI : Nontrivial V := Module.nontrivial_of_finrank_pos hPositive
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      have hExistsPartner : ∃ y : V, B x y ≠ 0 := by
        by_contra hNoPartner
        push Not at hNoPartner
        exact hx (hNondegenerate.1 x hNoPartner)
      obtain ⟨y, hxy_ne⟩ := hExistsPartner
      have hxy : B x y = 1 := zmod_two_eq_one_of_ne_zero _ hxy_ne
      have hPairIndependent : LinearIndependent (ZMod 2) ![x, y] := by
        rw [LinearIndependent.pair_iff]
        intro s t hCombination
        have hs := congrArg (fun z => B z y) hCombination
        have ht := congrArg (B x) hCombination
        have hsZero : s = 0 := by
          simpa [hxy, hAlt y, smul_eq_mul] using hs
        have htZero : t = 0 := by
          simpa [hxy, hAlt x, smul_eq_mul] using ht
        exact ⟨hsZero, htZero⟩
      let H : Submodule (ZMod 2) V :=
        Submodule.span (ZMod 2) (Set.range ![x, y])
      let pairBasis : Module.Basis (Fin 2) (ZMod 2) H :=
        Module.Basis.span hPairIndependent
      have pairBasis_zero : (pairBasis 0 : V) = x := by
        change ((Module.Basis.span hPairIndependent 0 : H) : V) = x
        rw [Module.Basis.span_apply]
        rfl
      have pairBasis_one : (pairBasis 1 : V) = y := by
        change ((Module.Basis.span hPairIndependent 1 : H) : V) = y
        rw [Module.Basis.span_apply]
        rfl
      have hPairNondegenerate : (B.restrict H).Nondegenerate := by
        have hyx : B y x = 1 := by
          rw [hSymm.eq]
          exact hxy
        refine ⟨?_, ?_⟩
        · intro z hz
          have hzInPairSpan : (z : V) ∈
              Submodule.span (ZMod 2) ({x, y} : Set V) := by
            simpa only [H, Matrix.range_cons_cons_empty] using z.2
          obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hzInPairSpan
          have hzX := hz ⟨x, by
            exact Submodule.subset_span (Set.mem_range_self 0)⟩
          have hzY := hz ⟨y, by
            exact Submodule.subset_span (Set.mem_range_self 1)⟩
          change B (z : V) x = 0 at hzX
          change B (z : V) y = 0 at hzY
          have ha : a = 0 := by
            rw [← hab] at hzY
            simpa [hxy, hAlt y, smul_eq_mul] using hzY
          have hb : b = 0 := by
            rw [← hab] at hzX
            simpa [hyx, hAlt x, smul_eq_mul] using hzX
          apply Subtype.ext
          simp [← hab, ha, hb]
        · intro z hz
          have hzInPairSpan : (z : V) ∈
              Submodule.span (ZMod 2) ({x, y} : Set V) := by
            simpa only [H, Matrix.range_cons_cons_empty] using z.2
          obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hzInPairSpan
          have hzX := hz ⟨x, by
            exact Submodule.subset_span (Set.mem_range_self 0)⟩
          have hzY := hz ⟨y, by
            exact Submodule.subset_span (Set.mem_range_self 1)⟩
          change B x (z : V) = 0 at hzX
          change B y (z : V) = 0 at hzY
          have ha : a = 0 := by
            rw [← hab] at hzY
            simpa [hyx, hAlt y, smul_eq_mul] using hzY
          have hb : b = 0 := by
            rw [← hab] at hzX
            simpa [hxy, hAlt x, smul_eq_mul] using hzX
          apply Subtype.ext
          simp [← hab, ha, hb]
      let W : Submodule (ZMod 2) V := B.orthogonal H
      have hComplement : IsCompl H W := by
        exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
          hSymm.isRefl hPairNondegenerate
      have hOrthogonalOrthogonal : B.orthogonal W = H := by
        change B.orthogonal (B.orthogonal H) = H
        exact LinearMap.BilinForm.orthogonal_orthogonal
          hNondegenerate hSymm.isRefl H
      have hWNondegenerate : (B.restrict W).Nondegenerate := by
        apply (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
          (B := B) hSymm.isRefl).2
        rw [hOrthogonalOrthogonal]
        exact hComplement.symm
      have hWAlt : (B.restrict W).IsAlt := by
        intro z
        exact hAlt z
      have hWSymm : (B.restrict W).IsSymm := by
        rw [LinearMap.BilinForm.isSymm_def]
        intro z w
        exact hSymm.eq z w
      have hPairDimension : Module.finrank (ZMod 2) H = 2 := by
        rw [Module.finrank_eq_card_basis pairBasis]
        simp
      have hWDimension : Module.finrank (ZMod 2) W = 2 * c := by
        have hOrthogonalDimension := LinearMap.BilinForm.finrank_orthogonal
          hNondegenerate H
        change Module.finrank (ZMod 2) W = _ at hOrthogonalDimension
        rw [hDimension, hPairDimension] at hOrthogonalDimension
        omega
      obtain ⟨remainingPairs⟩ :=
        ih (B.restrict W) hWAlt hWSymm hWNondegenerate hWDimension
      let combinedBasis :
          Module.Basis (Fin 2 ⊕ (Fin c ⊕ Fin c)) (ZMod 2) V :=
        (pairBasis.prod remainingPairs.basis).map
          (Submodule.prodEquivOfIsCompl H W hComplement)
      let resultBasis :
          Module.Basis (Fin (c + 1) ⊕ Fin (c + 1)) (ZMod 2) V :=
        combinedBasis.reindex (succIndexEquiv c)
      have resultBasis_inl_zero : resultBasis (Sum.inl 0) = x := by
        simp only [resultBasis, Module.Basis.reindex_apply,
          succIndexEquiv_symm_inl_zero, combinedBasis, Module.Basis.map_apply,
          Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
          LinearMap.inl_apply, Submodule.coe_prodEquivOfIsCompl']
        simpa using pairBasis_zero
      have resultBasis_inr_zero : resultBasis (Sum.inr 0) = y := by
        simp only [resultBasis, Module.Basis.reindex_apply,
          succIndexEquiv_symm_inr_zero, combinedBasis, Module.Basis.map_apply,
          Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
          LinearMap.inl_apply, Submodule.coe_prodEquivOfIsCompl']
        simpa using pairBasis_one
      have resultBasis_inl_succ (i : Fin c) :
          resultBasis (Sum.inl i.succ) = remainingPairs.basis (Sum.inl i) := by
        simp only [resultBasis, Module.Basis.reindex_apply,
          succIndexEquiv_symm_inl_succ, combinedBasis, Module.Basis.map_apply,
          Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
          LinearMap.inr_apply, Submodule.coe_prodEquivOfIsCompl']
        simp
      have resultBasis_inr_succ (i : Fin c) :
          resultBasis (Sum.inr i.succ) = remainingPairs.basis (Sum.inr i) := by
        simp only [resultBasis, Module.Basis.reindex_apply,
          succIndexEquiv_symm_inr_succ, combinedBasis, Module.Basis.map_apply,
          Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
          LinearMap.inr_apply, Submodule.coe_prodEquivOfIsCompl']
        simp
      have hPairOrthogonalRemaining (h : H) (w : W) : B h w = 0 := by
        exact w.2 h h.2
      have hRemainingOrthogonalPair (w : W) (h : H) : B w h = 0 := by
        rw [hSymm.eq]
        exact hPairOrthogonalRemaining h w
      refine ⟨{
        basis := resultBasis
        left_left := ?_
        right_right := ?_
        left_right := ?_ }⟩
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases ?_ (fun j => ?_) j
          · rw [resultBasis_inl_zero]
            exact hAlt x
          · rw [resultBasis_inl_zero, resultBasis_inl_succ]
            exact hPairOrthogonalRemaining ⟨x,
              Submodule.subset_span (Set.mem_range_self 0)⟩
              (remainingPairs.basis (Sum.inl j))
        · refine Fin.cases ?_ (fun j => ?_) j
          · rw [resultBasis_inl_succ, resultBasis_inl_zero]
            exact hRemainingOrthogonalPair
              (remainingPairs.basis (Sum.inl i)) ⟨x,
                Submodule.subset_span (Set.mem_range_self 0)⟩
          · rw [resultBasis_inl_succ, resultBasis_inl_succ]
            exact remainingPairs.left_left i j
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases ?_ (fun j => ?_) j
          · rw [resultBasis_inr_zero]
            exact hAlt y
          · rw [resultBasis_inr_zero, resultBasis_inr_succ]
            exact hPairOrthogonalRemaining ⟨y,
              Submodule.subset_span (Set.mem_range_self 1)⟩
              (remainingPairs.basis (Sum.inr j))
        · refine Fin.cases ?_ (fun j => ?_) j
          · rw [resultBasis_inr_succ, resultBasis_inr_zero]
            exact hRemainingOrthogonalPair
              (remainingPairs.basis (Sum.inr i)) ⟨y,
                Submodule.subset_span (Set.mem_range_self 1)⟩
          · rw [resultBasis_inr_succ, resultBasis_inr_succ]
            exact remainingPairs.right_right i j
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases ?_ (fun j => ?_) j
          · rw [resultBasis_inl_zero, resultBasis_inr_zero, hxy]
            simp
          · rw [resultBasis_inl_zero, resultBasis_inr_succ]
            have hOrthogonal := hPairOrthogonalRemaining ⟨x,
              Submodule.subset_span (Set.mem_range_self 0)⟩
              (remainingPairs.basis (Sum.inr j))
            simpa using hOrthogonal
        · refine Fin.cases ?_ (fun j => ?_) j
          · rw [resultBasis_inl_succ, resultBasis_inr_zero]
            have hOrthogonal := hRemainingOrthogonalPair
              (remainingPairs.basis (Sum.inl i)) ⟨y,
                Submodule.subset_span (Set.mem_range_self 1)⟩
            simpa using hOrthogonal
          · rw [resultBasis_inl_succ, resultBasis_inr_succ]
            simpa using remainingPairs.left_right i j

theorem right_left
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} {c : ℕ}
    (P : SymplecticPairBasis B c) (hSymm : B.IsSymm)
    (i j : Fin c) :
    B (P.basis (Sum.inr i)) (P.basis (Sum.inl j)) =
      if i = j then 1 else 0 := by
  rw [hSymm.eq]
  simpa [eq_comm] using P.left_right j i

private theorem castAdd_ne_addNat
    {c : ℕ} (i j : Fin c) :
    Fin.castAdd c i ≠ Fin.addNat j c := by
  intro h
  have hval := congrArg Fin.val h
  simp [Fin.castAdd] at hval
  omega

private theorem addNat_ne_castAdd
    {c : ℕ} (i j : Fin c) :
    Fin.addNat i c ≠ Fin.castAdd c j :=
  Ne.symm (castAdd_ne_addNat j i)

/- 标准坐标基的辛内积。以下证明成对辛基的坐标映射保持辛内积。
-/
private theorem symplecticBilinear_single_X_X
    {c : ℕ} (i j : Fin c) :
    NQubitPauliOperator.symplecticBilinear
        (Pi.single (Fin.castAdd c i) (1 : ZMod 2))
        (Pi.single (Fin.castAdd c j) 1) = 0 := by
  simp [NQubitPauliOperator.symplecticBilinear, Pi.single_apply,
    addNat_ne_castAdd]

private theorem symplecticBilinear_single_Z_Z
    {c : ℕ} (i j : Fin c) :
    NQubitPauliOperator.symplecticBilinear
        (Pi.single (Fin.addNat i c) (1 : ZMod 2))
        (Pi.single (Fin.addNat j c) 1) = 0 := by
  simp [NQubitPauliOperator.symplecticBilinear, Pi.single_apply,
    castAdd_ne_addNat]

private theorem symplecticBilinear_single_X_Z
    {c : ℕ} (i j : Fin c) :
    NQubitPauliOperator.symplecticBilinear
        (Pi.single (Fin.castAdd c i) (1 : ZMod 2))
        (Pi.single (Fin.addNat j c) 1) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [NQubitPauliOperator.symplecticBilinear, Pi.single_apply,
      castAdd_ne_addNat, addNat_ne_castAdd]
  · have hji : j ≠ i := Ne.symm hij
    simp [NQubitPauliOperator.symplecticBilinear, Pi.single_apply,
      castAdd_ne_addNat, addNat_ne_castAdd, hij, hji]

private theorem symplecticBilinear_single_Z_X
    {c : ℕ} (i j : Fin c) :
    NQubitPauliOperator.symplecticBilinear
        (Pi.single (Fin.addNat i c) (1 : ZMod 2))
        (Pi.single (Fin.castAdd c j) 1) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [NQubitPauliOperator.symplecticBilinear, Pi.single_apply,
      castAdd_ne_addNat, addNat_ne_castAdd]
  · have hji : j ≠ i := Ne.symm hij
    simp [NQubitPauliOperator.symplecticBilinear, Pi.single_apply,
      castAdd_ne_addNat, addNat_ne_castAdd, hij, hji]

theorem symplecticBilinear_toStandardCoordinates
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} {c : ℕ}
    (P : SymplecticPairBasis B c) (hSymm : B.IsSymm)
    (v w : V) :
    NQubitPauliOperator.symplecticBilinear
        (P.toStandardCoordinates v) (P.toStandardCoordinates w) =
      B v w := by
  have hForms :
      (binarySymplecticBilinForm c).comp
          P.toStandardCoordinates.toLinearMap
          P.toStandardCoordinates.toLinearMap = B := by
    apply LinearMap.BilinForm.ext_basis P.basis
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · simp [LinearMap.BilinForm.comp_apply,
        symplecticBilinear_single_X_X, P.left_left]
    · simp [LinearMap.BilinForm.comp_apply,
        symplecticBilinear_single_X_Z, P.left_right]
    · simp [LinearMap.BilinForm.comp_apply,
        symplecticBilinear_single_Z_X, P.right_left hSymm]
    · simp [LinearMap.BilinForm.comp_apply,
        symplecticBilinear_single_Z_Z, P.right_right]
  exact congrArg (fun F => F v w) hForms

end SymplecticPairBasis

namespace BinarySymplecticSubspace

/- 将成对辛基写成标准二元辛坐标。最后分别选取纠缠部分与逻辑部分的标准辛基。
-/
abbrev StandardPairBasis {n : ℕ}
    (S : BinarySymplecticSubspace n) (c : ℕ) :=
  SymplecticPairBasis ((binarySymplecticBilinForm n).restrict S) c

theorem standardPairBasis_nonempty
    {n c : ℕ} (S : BinarySymplecticSubspace n)
    (hNondegenerate :
      ((binarySymplecticBilinForm n).restrict S).Nondegenerate)
    (hDimension : Module.finrank (ZMod 2) S = 2 * c) :
    Nonempty (StandardPairBasis S c) := by
  apply SymplecticPairBasis.nonempty_of_nondegenerate
    ((binarySymplecticBilinForm n).restrict S)
  · intro v
    exact binarySymplecticBilinForm_isAlt n v
  · rw [LinearMap.BilinForm.isSymm_def]
    intro v w
    exact (binarySymplecticBilinForm_isSymm n).eq v w
  · exact hNondegenerate
  · exact hDimension

noncomputable def standardPairBasis
    {n c : ℕ} (S : BinarySymplecticSubspace n)
    (hNondegenerate :
      ((binarySymplecticBilinForm n).restrict S).Nondegenerate)
    (hDimension : Module.finrank (ZMod 2) S = 2 * c) :
    StandardPairBasis S c :=
  Classical.choice (standardPairBasis_nonempty S hNondegenerate hDimension)

namespace RadicalDecomposition

noncomputable def entanglementPairBasis
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    StandardPairBasis D.nondegeneratePart c :=
  standardPairBasis D.nondegeneratePart
    D.nondegeneratePart_isNondegenerate
    (D.nondegeneratePart_finrank_eq_two_mul_of_hasType hType)

end RadicalDecomposition

namespace LogicalDecomposition

noncomputable def logicalPairBasis
    {n m l c k : ℕ} (A : EASymplecticData n m l c k)
    (D : LogicalDecomposition A.stabilizerSpace) :
    StandardPairBasis D.logicalPart k :=
  standardPairBasis D.logicalPart D.logicalPart_isNondegenerate
    (D.logicalPart_finrank_eq_two_mul_logicalDimension A)

end LogicalDecomposition

end BinarySymplecticSubspace
end Quantum
