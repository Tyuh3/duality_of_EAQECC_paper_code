import EAQECC.Minimality
import EAQECC.Symplectic.Basic
import QEC.Stabilizer.Framework.Symplectic.SymplecticOrthogonal
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
二元辛生成矩阵与抽象子空间模型的衔接。把矩阵行转换为候选 Pauli 生成元，
联系辛内积矩阵、冲突秩及子空间类型，并推出固定候选生成元的纠缠数下界。
-/

namespace Quantum
namespace SymplecticType

/- 从二元辛生成矩阵构造 Pauli 生成元列表。以下证明行线性无关时得到合法候选生成元。
-/
def symplecticGeneratorList {m n : ℕ}
    (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2)) :
    List (NQubitPauliGroupElement n) :=
  List.ofFn fun i : Fin m => binarySymplecticVectorToPauli (P.row i)

@[simp] theorem symplecticGeneratorList_length
    {m n : ℕ} (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2)) :
    (symplecticGeneratorList P).length = m := by
  simp [symplecticGeneratorList]

theorem symplecticGeneratorList_checkMatrix_eq
    {m n : ℕ} (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2)) :
    NQubitPauliGroupElement.checkMatrix (symplecticGeneratorList P) =
      P.row ∘ finCongr (symplecticGeneratorList_length P) := by
  funext i j
  unfold NQubitPauliGroupElement.checkMatrix
  simp only [symplecticGeneratorList, List.get_ofFn, Function.comp_apply]
  rw [binarySymplecticVectorToPauli_toSymplectic]
  apply congrArg (fun a : Fin m => P a j)
  apply Fin.ext
  change (i : ℕ) = (finCongr _ i : ℕ)
  rfl

theorem symplecticGeneratorList_rowsLinearIndependent
    {m n : ℕ} (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2))
    (hP : LinearIndependent (ZMod 2) P.row) :
    NQubitPauliGroupElement.rowsLinearIndependent
      (symplecticGeneratorList P) := by
  rw [NQubitPauliGroupElement.rowsLinearIndependent,
    symplecticGeneratorList_checkMatrix_eq]
  exact
    (linearIndependent_equiv
      (finCongr (symplecticGeneratorList_length P))).mpr hP

def symplecticGeneratorCandidate
    {m n : ℕ} (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2))
    (hP : LinearIndependent (ZMod 2) P.row) :
    GeneratorListCandidate n where
  generatorsList := symplecticGeneratorList P
  generators_phaseZero := by
    apply NQubitPauliGroupElement.AllPhaseZero_ofFn
    intro i
    simp [binarySymplecticVectorToPauli]
  generators_rowsIndependent :=
    symplecticGeneratorList_rowsLinearIndependent P hP

/- 矩阵行之间的辛内积矩阵、行空间和标准辛形式矩阵。
以下证明辛内积矩阵等于生成矩阵、标准辛矩阵与转置的乘积，并与候选生成元的冲突矩阵一致。
-/
def symplecticGramMatrix {m n : ℕ}
    (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2)) :
    Matrix (Fin m) (Fin m) (ZMod 2) :=
  fun i j =>
    NQubitPauliOperator.symplecticBilinear (P.row i) (P.row j)

abbrev symplecticMatrixRowSpace {m n : ℕ}
    (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2)) :
    BinarySymplecticSubspace n :=
  Submodule.span (ZMod 2) (Set.range P.row)

def standardSymplecticMatrix (n : ℕ) :
    Matrix (Fin (n + n)) (Fin (n + n)) (ZMod 2) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (auxSymplecticMatrix n)

private theorem symplecticGramMatrix_eq_reindexed_mul_auxSymplecticMatrix
    {m n : ℕ} (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2)) :
    symplecticGramMatrix P =
      Matrix.reindex (Equiv.refl (Fin m)) finSumFinEquiv.symm P *
        auxSymplecticMatrix n *
        (Matrix.reindex (Equiv.refl (Fin m)) finSumFinEquiv.symm P).transpose := by
  ext i j
  simp [symplecticGramMatrix, NQubitPauliOperator.symplecticBilinear,
    auxSymplecticMatrix, Matrix.reindex_apply, Matrix.mul_apply]
  rw [Finset.sum_add_distrib]
  abel

theorem symplecticGramMatrix_eq_mul_standardSymplecticMatrix_mul_transpose
    {m n : ℕ} (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2)) :
    symplecticGramMatrix P =
      P * standardSymplecticMatrix n * P.transpose := by
  let e : (Fin n ⊕ Fin n) ≃ Fin (n + n) := finSumFinEquiv
  let Q : Matrix (Fin m) (Fin n ⊕ Fin n) (ZMod 2) :=
    Matrix.reindex (Equiv.refl (Fin m)) e.symm P
  have hP : Matrix.reindex (Equiv.refl (Fin m)) e Q = P := by
    ext i j
    simp [Q, Matrix.reindex_apply]
  have hmulLeft :
      Matrix.reindex (Equiv.refl (Fin m)) e Q *
          Matrix.reindex e e (auxSymplecticMatrix n) =
        Matrix.reindex (Equiv.refl (Fin m)) e
          (Q * auxSymplecticMatrix n) := by
    exact Matrix.reindexLinearEquiv_mul
      (R := ZMod 2) (A := ZMod 2)
      (Equiv.refl (Fin m)) e e Q (auxSymplecticMatrix n)
  have hmulRight :
      Matrix.reindex (Equiv.refl (Fin m)) e
          (Q * auxSymplecticMatrix n) *
          Matrix.reindex e (Equiv.refl (Fin m)) Q.transpose =
        Matrix.reindex (Equiv.refl (Fin m)) (Equiv.refl (Fin m))
          (Q * auxSymplecticMatrix n * Q.transpose) := by
    exact Matrix.reindexLinearEquiv_mul
      (R := ZMod 2) (A := ZMod 2)
      (Equiv.refl (Fin m)) e (Equiv.refl (Fin m))
      (Q * auxSymplecticMatrix n) Q.transpose
  calc
    symplecticGramMatrix P =
        Q * auxSymplecticMatrix n * Q.transpose := by
      simpa [Q, e] using
        symplecticGramMatrix_eq_reindexed_mul_auxSymplecticMatrix P
    _ = Matrix.reindex (Equiv.refl (Fin m)) e Q *
          Matrix.reindex e e (auxSymplecticMatrix n) *
          (Matrix.reindex (Equiv.refl (Fin m)) e Q).transpose := by
      symm
      rw [hmulLeft, Matrix.transpose_reindex, hmulRight]
      exact Matrix.reindex_refl_refl _
    _ = P * standardSymplecticMatrix n * P.transpose := by
      rw [hP]
      rfl

def symplecticGeneratorIndexEquiv {m n : ℕ}
    (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2)) :
    Fin (symplecticGeneratorList P).length ≃ Fin m :=
  finCongr (symplecticGeneratorList_length P)

@[simp] theorem symplecticGeneratorCandidate_get
    {m n : ℕ} (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2))
    (hP : LinearIndependent (ZMod 2) P.row) (i : Fin m) :
    (symplecticGeneratorCandidate P hP).generatorsList.get
        ((symplecticGeneratorIndexEquiv P).symm i) =
      binarySymplecticVectorToPauli (P.row i) := by
  unfold symplecticGeneratorCandidate symplecticGeneratorIndexEquiv
  unfold symplecticGeneratorList
  simp only [List.get_ofFn]
  apply congrArg (fun a : Fin m => binarySymplecticVectorToPauli (P.row a))
  apply Fin.ext
  rfl

theorem symplecticGeneratorCandidate_conflictMatrix_eq_symplecticGram
    {m n : ℕ} (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2))
    (hP : LinearIndependent (ZMod 2) P.row) :
    Matrix.reindex (symplecticGeneratorIndexEquiv P)
        (symplecticGeneratorIndexEquiv P)
        (GeneratorListCandidate.conflictMatrix
          (symplecticGeneratorCandidate P hP)) =
      symplecticGramMatrix P := by
  ext i j
  rw [Matrix.reindex_apply]
  unfold Matrix.submatrix
  simp only [Matrix.of_apply]
  rw [GeneratorListCandidate.conflictMatrix_apply]
  rw [symplecticGeneratorCandidate_get, symplecticGeneratorCandidate_get]
  rw [← NQubitPauliOperator.symplecticBilinear_toSymplectic]
  simp only [binarySymplecticVectorToPauli_toSymplectic]
  rfl

theorem symplecticGeneratorCandidate_conflictRank_eq_symplecticGramRank
    {m n : ℕ} (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2))
    (hP : LinearIndependent (ZMod 2) P.row) :
    GeneratorListCandidate.conflictRank
        (symplecticGeneratorCandidate P hP) =
      Matrix.rank (symplecticGramMatrix P) := by
  unfold GeneratorListCandidate.conflictRank
  calc
    Matrix.rank (GeneratorListCandidate.conflictMatrix
        (symplecticGeneratorCandidate P hP)) =
        Matrix.rank (Matrix.reindex (symplecticGeneratorIndexEquiv P)
          (symplecticGeneratorIndexEquiv P)
          (GeneratorListCandidate.conflictMatrix
            (symplecticGeneratorCandidate P hP))) :=
      (Matrix.rank_reindex (symplecticGeneratorIndexEquiv P)
        (symplecticGeneratorIndexEquiv P)
        (GeneratorListCandidate.conflictMatrix
          (symplecticGeneratorCandidate P hP))).symm
    _ = Matrix.rank (symplecticGramMatrix P) := by
      rw [symplecticGeneratorCandidate_conflictMatrix_eq_symplecticGram]

/-- 矩阵的辛秩条件。要求行之间的辛内积矩阵秩为 2c。
以下在矩阵行线性无关的条件下，证明它等价于行空间具有辛类型 [m,c]ₛ。
-/
def HasSymplecticType {m n : ℕ}
    (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2))
    (c : ℕ) : Prop :=
  Matrix.rank (symplecticGramMatrix P) = 2 * c

theorem hasSymplecticType_iff_rowSpace_hasType
    {m n c : ℕ}
    (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2))
    (hP : LinearIndependent (ZMod 2) P.row) :
    HasSymplecticType P c ↔
      (symplecticMatrixRowSpace P).HasType m c := by
  let S := symplecticMatrixRowSpace P
  let b : Module.Basis (Fin m) (ZMod 2) S := Module.Basis.span hP
  let B := (binarySymplecticBilinForm n).restrict S

  have hDimension : Module.finrank (ZMod 2) S = m := by
    rw [show S = Submodule.span (ZMod 2) (Set.range P.row) from rfl]
    rw [← Matrix.rank_eq_finrank_span_row]
    simpa using hP.rank_matrix

  have hGramMatrix :
      LinearMap.BilinForm.toMatrix b B = symplecticGramMatrix P := by
    ext i j
    simp [b, B, S, symplecticGramMatrix,
      binarySymplecticBilinForm_apply]

  have hRank :
      S.symplecticRank = Matrix.rank (symplecticGramMatrix P) := by
    have hBSymmetric : B.IsSymm := by
      simpa [B] using (binarySymplecticBilinForm_isSymm n).restrict S
    let M : Matrix (Fin m) (Fin m) (ZMod 2) :=
      LinearMap.toMatrix b b.dualBasis B
    have hMatrix : M = LinearMap.BilinForm.toMatrix b B := by
      ext i j
      simp only [M, LinearMap.toMatrix_apply,
        LinearMap.BilinForm.toMatrix_apply,
        Module.Basis.dualBasis_repr]
      exact hBSymmetric.eq (b j) (b i)
    have hMatrixRank :=
      Matrix.rank_eq_finrank_range_toLin M b.dualBasis b
    rw [Matrix.toLin_toMatrix] at hMatrixRank
    unfold BinarySymplecticSubspace.symplecticRank
    rw [show (binarySymplecticBilinForm n).restrict S = B from rfl]
    rw [← hMatrixRank, hMatrix, hGramMatrix]

  constructor
  · intro hType
    exact ⟨hDimension, hRank.trans hType⟩
  · intro hType
    exact hRank.symm.trans hType.2

/- 由矩阵辛类型得到候选生成元的纠缠参数，并证明任意恢复同一候选列表的扩展至少需要 c 个辅助量子比特。
-/
theorem symplecticGeneratorCandidate_ebitCount_eq_of_hasSymplecticType
    {m n c : ℕ} (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2))
    (hP : LinearIndependent (ZMod 2) P.row)
    (hType : HasSymplecticType P c) :
    GeneratorListCandidate.ebitCount
        (symplecticGeneratorCandidate P hP) =
      c := by
  unfold GeneratorListCandidate.ebitCount
  rw [symplecticGeneratorCandidate_conflictRank_eq_symplecticGramRank,
    hType]
  omega

theorem symplecticTypeParameter_le_of_canExtendWith
    {m n c c' : ℕ} (P : Matrix (Fin m) (Fin (n + n)) (ZMod 2))
    (hP : LinearIndependent (ZMod 2) P.row)
    (hType : HasSymplecticType P c)
    (hExtend : CanExtendWith (symplecticGeneratorCandidate P hP) c') :
    c ≤ c' := by
  calc
    c = GeneratorListCandidate.ebitCount
        (symplecticGeneratorCandidate P hP) :=
      (symplecticGeneratorCandidate_ebitCount_eq_of_hasSymplecticType
        P hP hType).symm
    _ ≤ c' :=
      GeneratorListCandidate.ebitCount_le_of_canExtendWith
        (symplecticGeneratorCandidate P hP) hExtend

end SymplecticType
end Quantum
