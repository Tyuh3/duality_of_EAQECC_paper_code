import EAQECC.Applications.BinaryEuclideanHullEAQECC
import EAQECC.Applications.SymplecticTypeEAQECC
import EAQECC.Symplectic.Distance
import EAQECC.Symplectic.EACode

/-!
Kim 二元码实例。由校验矩阵构造 CSS 辛子空间，证明辛对偶、根空间和两侧距离，
再调用一般模型构造参数 [[12,5,3;3]] 与 [[12,3,3;5]] 的纠缠辅助对偶码。
-/

namespace Quantum.Kim2023BinaryExample

open BinaryEuclideanHull
open BinaryEuclideanHull.BinaryCode12_7_3EuclideanHull2

/- 由校验矩阵的纯 X、纯 Z 行组成辛矩阵并取行空间。
以下证明该空间维数为 10、限制辛形式秩为 6、根空间维数为 4。
-/
def matrix : Matrix (Fin 10) (Fin 24) (ZMod 2) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv cssSymplecticMatrix

noncomputable def space : BinarySymplecticSubspace 12 :=
  SymplecticType.symplecticMatrixRowSpace matrix

private theorem matrixRows_eq_generatorFamily :
    matrix.row =
      (fun i : Fin 10 =>
        NQubitPauliOperator.toSymplectic
          (parityCheckCSSGeneratorFamily parityCheckMatrix i).operators) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, cssSymplecticMatrix,
      parityCheckCSSSymplecticMatrix,
      parityCheckCSSGeneratorFamily,
      Matrix.reindex_apply, parityCheckMatrix] <;>
    native_decide

theorem matrix_rowsLinearIndependent :
    LinearIndependent (ZMod 2) matrix.row := by
  rw [matrixRows_eq_generatorFamily]
  exact parityCheckCSSGeneratorFamily_rowsLinearIndependent
    parityCheckMatrix parityCheckRowsLinearIndependent

theorem space_finrank :
    Module.finrank (ZMod 2) space = 10 := by
  let b : Module.Basis (Fin 10) (ZMod 2) space :=
    Module.Basis.span matrix_rowsLinearIndependent
  simpa [space, SymplecticType.symplecticMatrixRowSpace] using
    Module.finrank_eq_card_basis b

private theorem symplecticGram_eq_reindexedConflict :
    SymplecticType.symplecticGramMatrix (m := 10) (n := 12) matrix =
      Matrix.reindex finSumFinEquiv finSumFinEquiv cssConflictMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SymplecticType.symplecticGramMatrix, matrix,
      cssConflictMatrix, cssSymplecticMatrix,
      parityCheckCSSConflictMatrix,
      parityCheckCSSSymplecticMatrix,
      Matrix.reindex_apply, NQubitPauliOperator.symplecticBilinear,
      parityCheckMatrix] <;>
    native_decide

theorem matrix_symplecticGram_rank :
    Matrix.rank
      (SymplecticType.symplecticGramMatrix (m := 10) (n := 12) matrix) = 6 := by
  rw [symplecticGram_eq_reindexedConflict, Matrix.rank_reindex]
  rw [cssConflictMatrix_rank, parityCheckGramRank]

theorem space_hasType :
    space.HasType 10 3 := by
  have hMatrixType :
      @SymplecticType.HasSymplecticType 10 12 matrix 3 := by
    unfold SymplecticType.HasSymplecticType
    simpa using matrix_symplecticGram_rank
  have hRowSpace :=
    (SymplecticType.hasSymplecticType_iff_rowSpace_hasType
      (m := 10) (n := 12) (c := 3)
      matrix matrix_rowsLinearIndependent).mp hMatrixType
  simpa only [space] using hRowSpace

theorem radical_finrank :
    Module.finrank (ZMod 2) (symplecticRadical space) = 4 := by
  have hDimension :
      Module.finrank (ZMod 2) (symplecticRadical space) + 2 * 3 = 10 :=
    BinarySymplecticSubspace.radicalFinrank_add_two_mul_eq_of_hasType
      space_hasType
  omega

/- 辛向量的 X、Z 分量以及由同一二元子空间的两份分量组成的 CSS 空间。
以下用纯 X、纯 Z 向量描述其坐标，并将本实例空间写成校验矩阵行空间的 CSS 空间。
-/
private def xProjection (n : ℕ) :
    BinarySymplecticVector n →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun v i := v (Fin.castAdd n i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def zProjection (n : ℕ) :
    BinarySymplecticVector n →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun v i := v (Fin.natAdd n i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cssSpace {n : ℕ} (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    BinarySymplecticSubspace n :=
  D.comap (xProjection n) ⊓ D.comap (zProjection n)

@[simp] private theorem mem_cssSpace_iff
    {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {v : BinarySymplecticVector n} :
    v ∈ cssSpace D ↔ xProjection n v ∈ D ∧ zProjection n v ∈ D := by
  rfl

private def pureXVector {n : ℕ} (x : Fin n → ZMod 2) :
    BinarySymplecticVector n :=
  NQubitPauliOperator.toSymplectic
    (binaryVectorToPureXPauli x).operators

private def pureZVector {n : ℕ} (z : Fin n → ZMod 2) :
    BinarySymplecticVector n :=
  NQubitPauliOperator.toSymplectic
    (binaryVectorToPureZPauli z).operators

@[simp] private theorem xProjection_pureX
    {n : ℕ} (x : Fin n → ZMod 2) :
    xProjection n (pureXVector x) = x := by
  funext i
  simp [xProjection, pureXVector]

@[simp] private theorem zProjection_pureX
    {n : ℕ} (x : Fin n → ZMod 2) :
    zProjection n (pureXVector x) = 0 := by
  funext i
  simp [zProjection, pureXVector]

@[simp] private theorem xProjection_pureZ
    {n : ℕ} (z : Fin n → ZMod 2) :
    xProjection n (pureZVector z) = 0 := by
  funext i
  simp [xProjection, pureZVector]

@[simp] private theorem zProjection_pureZ
    {n : ℕ} (z : Fin n → ZMod 2) :
    zProjection n (pureZVector z) = z := by
  funext i
  simp [zProjection, pureZVector]

private theorem pureX_add_pureZ_parts
    {n : ℕ} (v : BinarySymplecticVector n) :
    pureXVector (xProjection n v) + pureZVector (zProjection n v) = v := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [pureXVector, pureZVector, xProjection, zProjection]

private theorem pureXVector_linearCombination
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (a : Fin r → ZMod 2) :
    pureXVector (H.vecMulLinear a) =
      ∑ i, a i • pureXVector (H.row i) := by
  funext j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · simp [pureXVector, Matrix.vecMulLinear, Matrix.vecMul, dotProduct]
  · simp [pureXVector]

private theorem pureZVector_linearCombination
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (a : Fin r → ZMod 2) :
    pureZVector (H.vecMulLinear a) =
      ∑ i, a i • pureZVector (H.row i) := by
  funext j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · simp [pureZVector]
  · simp [pureZVector, Matrix.vecMulLinear, Matrix.vecMul, dotProduct]

private theorem matrix_row_x (i : Fin 5) :
    matrix.row (Fin.castAdd 5 i) = pureXVector (parityCheckMatrix.row i) := by
  rw [matrixRows_eq_generatorFamily]
  funext j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j <;>
    simp [parityCheckCSSGeneratorFamily, pureXVector]

private theorem matrix_row_z (i : Fin 5) :
    matrix.row (Fin.natAdd 5 i) = pureZVector (parityCheckMatrix.row i) := by
  rw [matrixRows_eq_generatorFamily]
  change NQubitPauliOperator.toSymplectic
      (parityCheckCSSGeneratorFamily parityCheckMatrix
        (Fin.natAdd 5 i)).operators = _
  rw [parityCheckCSSGeneratorFamily_z]
  rfl

theorem space_eq_cssSpace_parityCheck :
    space = cssSpace (matrixRowSpace parityCheckMatrix) := by
  apply le_antisymm
  · rw [space, SymplecticType.symplecticMatrixRowSpace]
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact Fin.addCases
      (motive := fun i =>
        matrix.row i ∈ cssSpace (matrixRowSpace parityCheckMatrix))
      (fun a : Fin 5 => by
        change matrix.row (Fin.castAdd 5 a) ∈
          cssSpace (matrixRowSpace parityCheckMatrix)
        rw [matrix_row_x]
        constructor
        · exact ⟨Pi.single a 1, by simp [Matrix.vecMulLinear]⟩
        · simp)
      (fun a : Fin 5 => by
        change matrix.row (Fin.natAdd 5 a) ∈
          cssSpace (matrixRowSpace parityCheckMatrix)
        rw [matrix_row_z]
        constructor
        · simp
        · exact ⟨Pi.single a 1, by simp [Matrix.vecMulLinear]⟩)
      i
  · intro v hv
    rcases hv.1 with ⟨a, ha⟩
    rcases hv.2 with ⟨b, hb⟩
    rw [← pureX_add_pureZ_parts v]
    rw [← ha, ← hb]
    apply Submodule.add_mem
    · rw [pureXVector_linearCombination]
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem _ _
        (by
          rw [← matrix_row_x]
          exact Submodule.subset_span (Set.mem_range_self _))
    · rw [pureZVector_linearCombination]
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem _ _
        (by
          rw [← matrix_row_z]
          exact Submodule.subset_span (Set.mem_range_self _))

private theorem sympOrthogonal_cssSpace
    {n : ℕ} (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    NQubitPauliGroupElement.sympOrthogonal (cssSpace D) =
      cssSpace ((euclideanBilinForm n).orthogonal D) := by
  ext v
  rw [BinarySymplecticSubspace.mem_sympOrthogonal_iff_bilinForm]
  constructor
  · intro hv
    constructor
    · change xProjection n v ∈
        (euclideanBilinForm n).orthogonal D
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      change dotProduct y (xProjection n v) = 0
      have hPair := hv (pureZVector y) (by
        constructor <;> simp [hy])
      simpa [binarySymplecticBilinForm_apply,
        NQubitPauliOperator.symplecticBilinear,
        dotProduct, xProjection, pureZVector, mul_comm] using hPair
    · change zProjection n v ∈
        (euclideanBilinForm n).orthogonal D
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      change dotProduct y (zProjection n v) = 0
      have hPair := hv (pureXVector y) (by
        constructor <;> simp [hy])
      simpa [binarySymplecticBilinForm_apply,
        NQubitPauliOperator.symplecticBilinear,
        dotProduct, zProjection, pureXVector, mul_comm] using hPair
  · rintro ⟨hx, hz⟩ w ⟨hwx, hwz⟩
    change xProjection n v ∈
      (euclideanBilinForm n).orthogonal D at hx
    change zProjection n v ∈
      (euclideanBilinForm n).orthogonal D at hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx hz
    have hFirst := hx (zProjection n w) hwz
    have hSecond := hz (xProjection n w) hwx
    change dotProduct (zProjection n w) (xProjection n v) = 0 at hFirst
    change dotProduct (xProjection n w) (zProjection n v) = 0 at hSecond
    simp only [binarySymplecticBilinForm_apply,
      NQubitPauliOperator.symplecticBilinear, Finset.sum_add_distrib]
    calc
      (∑ i, v (Fin.castAdd n i) * w (Fin.natAdd n i)) +
          ∑ i, v (Fin.natAdd n i) * w (Fin.castAdd n i) =
          dotProduct (zProjection n w) (xProjection n v) +
            dotProduct (xProjection n w) (zProjection n v) := by
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro i _ <;>
                simp [xProjection, zProjection, mul_comm]
      _ = 0 := by rw [hFirst, hSecond, zero_add]

/-- Kim 二元辛空间的辛对偶。
本实例的输入空间由校验矩阵行空间构成，其辛对偶由生成矩阵行空间构成。
证明复用 CSS 空间的对偶对应及生成矩阵与校验矩阵的欧几里得对偶关系。
-/
theorem sympOrthogonal_space_eq_cssSpace_generator :
    NQubitPauliGroupElement.sympOrthogonal space =
      cssSpace (matrixRowSpace kimGeneratorMatrix) := by
  rw [space_eq_cssSpace_parityCheck, sympOrthogonal_cssSpace]
  congr 1
  have hTranspose :
      parityCheckMatrix * kimGeneratorMatrix.transpose = 0 := by
    have h := congrArg Matrix.transpose
      generator_mul_parityCheckTranspose
    simpa using h
  exact generatorRowSpace_orthogonal_eq_parityCheckRowSpace
    parityCheckMatrix kimGeneratorMatrix
    parityCheckRowsLinearIndependent generatorRowsLinearIndependent
    hTranspose (by norm_num)

/- CSS 空间保持子空间交。以下由此把辛根空间写成经典码欧几里得交空间的两份分量。
-/
private theorem cssSpace_inf
    {n : ℕ} (D E : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    cssSpace (D ⊓ E) = cssSpace D ⊓ cssSpace E := by
  ext v
  constructor
  · rintro ⟨⟨hxD, hxE⟩, hzD, hzE⟩
    exact ⟨⟨hxD, hzD⟩, hxE, hzE⟩
  · rintro ⟨⟨hxD, hzD⟩, hxE, hzE⟩
    exact ⟨⟨hxD, hxE⟩, hzD, hzE⟩

theorem radical_space_eq_cssSpace_generatorHull :
    symplecticRadical space =
      cssSpace (rowSpaceEuclideanRadical kimGeneratorMatrix) := by
  change space ⊓ NQubitPauliGroupElement.sympOrthogonal space = _
  rw [sympOrthogonal_space_eq_cssSpace_generator,
    space_eq_cssSpace_parityCheck,
    ← cssSpace_inf]
  congr 1
  change matrixRowSpace parityCheckMatrix ⊓
      matrixRowSpace kimGeneratorMatrix =
    matrixRowSpace kimGeneratorMatrix ⊓
      (euclideanBilinForm 12).orthogonal
        (matrixRowSpace kimGeneratorMatrix)
  rw [parityCheckRowSpace_eq_generatorRowSpace_orthogonal]
  exact inf_comm _ _

/- 二元支集、汉明重量及欧几里得交空间的成员判定。
以下对生成矩阵的 128 组及校验矩阵的 32 组二元行系数，在 Lean 内部有限判定：
不属于相应欧几里得交空间的码字重量不小于 3。这不能直接等同于经典码最小距离。
有限判定通过原生计算公理纳入证明，其计算部分依赖 Lean 编译器及运行时的正确性。
-/
private def binarySupport {n : ℕ} (x : Fin n → ZMod 2) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i ≠ 0

private def binaryWeight {n : ℕ} (x : Fin n → ZMod 2) : ℕ :=
  (binarySupport x).card

private theorem vecMul_mem_euclideanRadical_iff
    {r n : ℕ} (G : Matrix (Fin r) (Fin n) (ZMod 2))
    (a : Fin r → ZMod 2) :
    G.vecMulLinear a ∈ rowSpaceEuclideanRadical G ↔
      G.mulVec (G.vecMulLinear a) = 0 := by
  constructor
  · intro h
    have hOrthogonal := h.2
    rw [euclideanOrthogonal_rowSpace_eq_ker_mulVecLin] at hOrthogonal
    exact hOrthogonal
  · intro h
    constructor
    · exact ⟨a, rfl⟩
    · rw [euclideanOrthogonal_rowSpace_eq_ker_mulVecLin]
      exact h

private theorem generatorCombination_weight_lowerBound :
    ∀ a : Fin 7 → ZMod 2,
      kimGeneratorMatrix.mulVec (kimGeneratorMatrix.vecMulLinear a) ≠ 0 →
        3 ≤ binaryWeight (kimGeneratorMatrix.vecMulLinear a) := by
  native_decide

private theorem parityCheckCombination_weight_lowerBound :
    ∀ a : Fin 5 → ZMod 2,
      parityCheckMatrix.mulVec (parityCheckMatrix.vecMulLinear a) ≠ 0 →
        3 ≤ binaryWeight (parityCheckMatrix.vecMulLinear a) := by
  native_decide

/- 两侧达到重量下界的具体码字。以下验证它们重量为 3，且不属于相应欧几里得交空间。
-/
private def generatorWitnessCoefficients : Fin 7 → ZMod 2 :=
  ![0, 0, 0, 0, 0, 0, 1]

private def generatorWitness : Fin 12 → ZMod 2 :=
  kimGeneratorMatrix.vecMulLinear generatorWitnessCoefficients

private theorem generatorWitness_certificate :
    kimGeneratorMatrix.mulVec generatorWitness ≠ 0 ∧
      binaryWeight generatorWitness = 3 := by
  native_decide

private def parityCheckWitnessCoefficients : Fin 5 → ZMod 2 :=
  ![0, 0, 0, 0, 1]

private def parityCheckWitness : Fin 12 → ZMod 2 :=
  parityCheckMatrix.vecMulLinear parityCheckWitnessCoefficients

private theorem parityCheckWitness_certificate :
    parityCheckMatrix.mulVec parityCheckWitness ≠ 0 ∧
      binaryWeight parityCheckWitness = 3 := by
  native_decide

/- 纯 X、纯 Z 向量的辛重量等于二元重量，任意向量的分量重量不超过其辛重量。
-/
@[simp] private theorem symplecticWeight_pureX
    {n : ℕ} (x : Fin n → ZMod 2) :
    symplecticWeight (pureXVector x) = binaryWeight x := by
  unfold symplecticWeight symplecticSupport binaryWeight binarySupport
  congr 1
  ext i
  simp [pureXVector]

@[simp] private theorem symplecticWeight_pureZ
    {n : ℕ} (z : Fin n → ZMod 2) :
    symplecticWeight (pureZVector z) = binaryWeight z := by
  unfold symplecticWeight symplecticSupport binaryWeight binarySupport
  congr 1
  ext i
  simp [pureZVector]

private theorem binaryWeight_xProjection_le_symplecticWeight
    {n : ℕ} (v : BinarySymplecticVector n) :
    binaryWeight (xProjection n v) ≤ symplecticWeight v := by
  unfold binaryWeight binarySupport symplecticWeight symplecticSupport
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact Or.inl hi

private theorem binaryWeight_zProjection_le_symplecticWeight
    {n : ℕ} (v : BinarySymplecticVector n) :
    binaryWeight (zProjection n v) ≤ symplecticWeight v := by
  unfold binaryWeight binarySupport symplecticWeight symplecticSupport
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact Or.inr hi

/-- 原码侧最小辛重量为 3。
在辛对偶中排除根空间后，至少一个二元分量不属于欧几里得交空间，故辛重量至少为 3；
再用生成矩阵提供的重量为 3 的码字达到该下界。
-/
theorem originalSymplecticDistance :
    HasMinimumSymplecticWeightOutside
      (NQubitPauliGroupElement.sympOrthogonal space)
      (symplecticRadical space) 3 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro v hvOrthogonal hvRadical
    rw [sympOrthogonal_space_eq_cssSpace_generator] at hvOrthogonal
    rw [radical_space_eq_cssSpace_generatorHull] at hvRadical
    by_cases hxHull :
        xProjection 12 v ∈ rowSpaceEuclideanRadical kimGeneratorMatrix
    · have hzHull :
          zProjection 12 v ∉ rowSpaceEuclideanRadical kimGeneratorMatrix := by
        intro hz
        exact hvRadical ⟨hxHull, hz⟩
      rcases hvOrthogonal.2 with ⟨a, ha⟩
      have haOutside :
          kimGeneratorMatrix.vecMulLinear a ∉
            rowSpaceEuclideanRadical kimGeneratorMatrix := by
        intro h
        exact hzHull (ha ▸ h)
      have hSyndrome :
          kimGeneratorMatrix.mulVec (kimGeneratorMatrix.vecMulLinear a) ≠ 0 := by
        intro hZero
        exact haOutside
          ((vecMul_mem_euclideanRadical_iff kimGeneratorMatrix a).mpr hZero)
      calc
        3 ≤ binaryWeight (kimGeneratorMatrix.vecMulLinear a) :=
          generatorCombination_weight_lowerBound a hSyndrome
        _ = binaryWeight (zProjection 12 v) := congrArg binaryWeight ha
        _ ≤ symplecticWeight v :=
          binaryWeight_zProjection_le_symplecticWeight v
    · rcases hvOrthogonal.1 with ⟨a, ha⟩
      have haOutside :
          kimGeneratorMatrix.vecMulLinear a ∉
            rowSpaceEuclideanRadical kimGeneratorMatrix := by
        intro h
        exact hxHull (ha ▸ h)
      have hSyndrome :
          kimGeneratorMatrix.mulVec (kimGeneratorMatrix.vecMulLinear a) ≠ 0 := by
        intro hZero
        exact haOutside
          ((vecMul_mem_euclideanRadical_iff kimGeneratorMatrix a).mpr hZero)
      calc
        3 ≤ binaryWeight (kimGeneratorMatrix.vecMulLinear a) :=
          generatorCombination_weight_lowerBound a hSyndrome
        _ = binaryWeight (xProjection 12 v) := congrArg binaryWeight ha
        _ ≤ symplecticWeight v :=
          binaryWeight_xProjection_le_symplecticWeight v
  · refine ⟨pureXVector generatorWitness, ?_, ?_, ?_⟩
    · rw [sympOrthogonal_space_eq_cssSpace_generator]
      constructor
      · exact ⟨generatorWitnessCoefficients, by simp [generatorWitness]⟩
      · simp
    · rw [radical_space_eq_cssSpace_generatorHull]
      intro hRadical
      have hWord :
          generatorWitness ∈
            rowSpaceEuclideanRadical kimGeneratorMatrix := by
        simpa using hRadical.1
      exact generatorWitness_certificate.1
        ((vecMul_mem_euclideanRadical_iff
          kimGeneratorMatrix generatorWitnessCoefficients).mp hWord)
    · simpa using generatorWitness_certificate.2

/-- 对偶侧最小辛重量为 3。
对原辛空间中根空间之外的向量使用相同下界论证，并由校验矩阵提供达到下界的码字。
-/
theorem dualSymplecticDistance :
    HasMinimumSymplecticWeightOutside
      space (symplecticRadical space) 3 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro v hvSpace hvRadical
    rw [space_eq_cssSpace_parityCheck] at hvSpace
    rw [radical_space_eq_cssSpace_generatorHull] at hvRadical
    by_cases hxGeneratorHull :
        xProjection 12 v ∈ rowSpaceEuclideanRadical kimGeneratorMatrix
    · have hzGeneratorHull :
          zProjection 12 v ∉ rowSpaceEuclideanRadical kimGeneratorMatrix := by
        intro hz
        exact hvRadical ⟨hxGeneratorHull, hz⟩
      have hzParityCheckHull := hzGeneratorHull
      rw [generatorHull_eq_parityCheckHull] at hzParityCheckHull
      rcases hvSpace.2 with ⟨a, ha⟩
      have haOutside :
          parityCheckMatrix.vecMulLinear a ∉
            rowSpaceEuclideanRadical parityCheckMatrix := by
        intro h
        exact hzParityCheckHull (ha ▸ h)
      have hSyndrome :
          parityCheckMatrix.mulVec
              (parityCheckMatrix.vecMulLinear a) ≠ 0 := by
        intro hZero
        exact haOutside
          ((vecMul_mem_euclideanRadical_iff parityCheckMatrix a).mpr hZero)
      calc
        3 ≤ binaryWeight (parityCheckMatrix.vecMulLinear a) :=
          parityCheckCombination_weight_lowerBound a hSyndrome
        _ = binaryWeight (zProjection 12 v) := congrArg binaryWeight ha
        _ ≤ symplecticWeight v :=
          binaryWeight_zProjection_le_symplecticWeight v
    · have hxParityCheckHull := hxGeneratorHull
      rw [generatorHull_eq_parityCheckHull] at hxParityCheckHull
      rcases hvSpace.1 with ⟨a, ha⟩
      have haOutside :
          parityCheckMatrix.vecMulLinear a ∉
            rowSpaceEuclideanRadical parityCheckMatrix := by
        intro h
        exact hxParityCheckHull (ha ▸ h)
      have hSyndrome :
          parityCheckMatrix.mulVec
              (parityCheckMatrix.vecMulLinear a) ≠ 0 := by
        intro hZero
        exact haOutside
          ((vecMul_mem_euclideanRadical_iff parityCheckMatrix a).mpr hZero)
      calc
        3 ≤ binaryWeight (parityCheckMatrix.vecMulLinear a) :=
          parityCheckCombination_weight_lowerBound a hSyndrome
        _ = binaryWeight (xProjection 12 v) := congrArg binaryWeight ha
        _ ≤ symplecticWeight v :=
          binaryWeight_xProjection_le_symplecticWeight v
  · refine ⟨pureXVector parityCheckWitness, ?_, ?_, ?_⟩
    · rw [space_eq_cssSpace_parityCheck]
      constructor
      · exact ⟨parityCheckWitnessCoefficients,
          by simp [parityCheckWitness]⟩
      · simp
    · rw [radical_space_eq_cssSpace_generatorHull]
      intro hRadical
      have hGeneratorHull :
          parityCheckWitness ∈
            rowSpaceEuclideanRadical kimGeneratorMatrix := by
        simpa using hRadical.1
      have hParityCheckHull := hGeneratorHull
      rw [generatorHull_eq_parityCheckHull] at hParityCheckHull
      exact parityCheckWitness_certificate.1
        ((vecMul_mem_euclideanRadical_iff
          parityCheckMatrix parityCheckWitnessCoefficients).mp
            hParityCheckHull)
    · simpa using parityCheckWitness_certificate.2

/-- 将本实例的子空间、辛类型 [10,3]ₛ、根空间维数 4 及参数组织为一般二元辛输入。
-/
noncomputable def data : EASymplecticData 12 10 4 3 5 where
  stabilizerSpace := space
  hasType := space_hasType
  radical_finrank := radical_finrank
  parameter_eq := by norm_num

/-- Kim 实例的完整纠缠辅助码对偶结论。
调用一般二元辛空间对偶定理，并代入两侧距离为 3 的证明，
得到 [[12,5,3;3]] 与 [[12,3,3;5]] 两侧码的参数、稳定子空间及发送端正规化子对应。
-/
theorem symplecticEAQECCDualityInstance :
    (
      (5 = 12 + 3 - 10 ∧ 5 = 12 - 3 - 4) ∧
      StabilizerGroup.StabilizerCode.HasBaseDistance
        (n := 12) (c := 3) data.toStabilizerCode 3 ∧
      HasMinimumSymplecticWeightOutside
        (NQubitPauliGroupElement.sympOrthogonal space)
        (symplecticRadical space) 3 ∧
      RealizesEAStabilizerSpace
        (NQubitPauliGroupElement.sympSpan
          data.toStabilizerCode.generatorsList)
        space ∧
      {v : BinarySymplecticVector 12 |
        binarySymplecticVectorToPauli (baseSymplecticEmbedding 12 3 v) ∈
          StabilizerGroup.pauliNormalizer
            data.toStabilizerCode.toStabilizerGroup} =
        (NQubitPauliGroupElement.sympOrthogonal space :
          Set (BinarySymplecticVector 12))
    ) ∧
    (
      (3 = 12 + 5 - 14 ∧ 3 = 12 - 5 - 4) ∧
      BinarySymplecticSubspace.HasType
        (NQubitPauliGroupElement.sympOrthogonal space) 14 5 ∧
      StabilizerGroup.StabilizerCode.HasBaseDistance
        (n := 12) (c := 5) data.toDualStabilizerCode 3 ∧
      HasMinimumSymplecticWeightOutside
        space (symplecticRadical space) 3 ∧
      RealizesEAStabilizerSpace
        (NQubitPauliGroupElement.sympSpan
          data.toDualStabilizerCode.generatorsList)
        (NQubitPauliGroupElement.sympOrthogonal space) ∧
      {v : BinarySymplecticVector 12 |
        binarySymplecticVectorToPauli (baseSymplecticEmbedding 12 5 v) ∈
          StabilizerGroup.pauliNormalizer
            data.toDualStabilizerCode.toStabilizerGroup} =
        (space : Set (BinarySymplecticVector 12))
    ) := by
  have hSymplecticDuality := data.symplecticEAQECCDuality_full
  obtain
    ⟨⟨hParameter, hAlternativeParameter, hOriginalDistance,
        hOriginalRealizes, hOriginalNormalizer⟩,
      ⟨hDualDistance, hDualRealizes, hDualNormalizer⟩⟩ :=
    hSymplecticDuality

  have hOriginalMinimum :
      HasMinimumSymplecticWeightOutside
        (NQubitPauliGroupElement.sympOrthogonal data.stabilizerSpace)
        (symplecticRadical data.stabilizerSpace) 3 := by
    simpa [data] using originalSymplecticDistance
  obtain ⟨d, hOriginalCodeDistance, hMinimum⟩ :=
    hOriginalDistance (by norm_num)
  have hd : d = 3 := hMinimum.unique hOriginalMinimum
  subst d

  have hDualMinimum :
      HasMinimumSymplecticWeightOutside data.stabilizerSpace
        (symplecticRadical data.stabilizerSpace) 3 := by
    simpa [data] using dualSymplecticDistance
  obtain ⟨dDual, hDualCodeDistance, hMinimumDual⟩ :=
    hDualDistance (by norm_num)
  have hdDual : dDual = 3 := hMinimumDual.unique hDualMinimum
  subst dDual

  have hDualParameter : 3 = 12 + 5 - 14 := by
    exact data.symplecticDualData.parameter_eq
  have hDualAlternativeParameter : 3 = 12 - 5 - 4 := by
    exact
      data.symplecticDualData.logicalDimension_eq_length_sub_ebitCount_sub_radicalFinrank
  have hDualType :
      BinarySymplecticSubspace.HasType
        (NQubitPauliGroupElement.sympOrthogonal space) 14 5 := by
    simpa [data] using data.symplecticDual_hasType

  exact
    ⟨⟨⟨hParameter, hAlternativeParameter⟩,
        hOriginalCodeDistance, originalSymplecticDistance,
        by simpa [data] using hOriginalRealizes,
        by simpa [data] using hOriginalNormalizer⟩,
      ⟨⟨hDualParameter, hDualAlternativeParameter⟩,
        hDualType, hDualCodeDistance, dualSymplecticDistance,
        by simpa [data] using hDualRealizes,
        by simpa [data] using hDualNormalizer⟩⟩

/- 用一般模型封装原码和对偶码，并由完整实例结论赋予两侧发送端距离。
-/
noncomputable def originalCode : EACode 12 5 3 :=
  data.toEACode

noncomputable def dualCode : EACode 12 3 5 :=
  data.symplecticDualData.toEACode

@[simp] theorem originalCode_extendedCode :
    originalCode.extendedCode = data.toStabilizerCode := by
  rfl

@[simp] theorem dualCode_extendedCode :
    dualCode.extendedCode = data.toDualStabilizerCode := by
  rfl

noncomputable def originalCodeWithDistance :
    EACodeWithDistance 12 5 3 3 where
  toEACode := originalCode
  hasDistance := by
    change StabilizerGroup.StabilizerCode.HasBaseDistance
      (n := 12) (c := 3) originalCode.extendedCode 3
    simpa using symplecticEAQECCDualityInstance.1.2.1

noncomputable def dualCodeWithDistance :
    EACodeWithDistance 12 3 3 5 where
  toEACode := dualCode
  hasDistance := by
    change StabilizerGroup.StabilizerCode.HasBaseDistance
      (n := 12) (c := 5) dualCode.extendedCode 3
    simpa using symplecticEAQECCDualityInstance.2.2.2.1

/- 两侧码分别可用 3 和 5 个辅助量子比特构造；
后续复用一般下界，证明恢复同一候选生成元的扩展不能使用更少的辅助量子比特。
-/
noncomputable def originalReachability :
    CanExtendWith originalCode.generators 3 :=
  data.toEACode_canExtendWith

noncomputable def dualReachability :
    CanExtendWith dualCode.generators 5 :=
  data.symplecticDualData.toEACode_canExtendWith

theorem originalEbitLowerBound (c' : ℕ)
    (hExtension : CanExtendWith originalCode.generators c') :
    3 ≤ c' :=
  originalCode.c_minimal hExtension

theorem dualEbitLowerBound (c' : ℕ)
    (hExtension : CanExtendWith dualCode.generators c') :
    5 ≤ c' :=
  dualCode.c_minimal hExtension

theorem dualConstruction :
    (
      NQubitPauliGroupElement.sympSpan
          originalCode.generators.generatorsList = space ∧
      originalCode.extendedCode = data.toStabilizerCode ∧
      originalCode.HasDistance 3 ∧
      GeneratorListCandidate.ebitCount originalCode.generators = 3 ∧
      Nonempty (CanExtendWith originalCode.generators 3) ∧
      ∀ c' : ℕ, CanExtendWith originalCode.generators c' → 3 ≤ c'
    ) ∧
    (
      NQubitPauliGroupElement.sympSpan
          dualCode.generators.generatorsList =
        NQubitPauliGroupElement.sympOrthogonal space ∧
      dualCode.extendedCode = data.toDualStabilizerCode ∧
      dualCode.HasDistance 3 ∧
      GeneratorListCandidate.ebitCount dualCode.generators = 5 ∧
      Nonempty (CanExtendWith dualCode.generators 5) ∧
      ∀ c' : ℕ, CanExtendWith dualCode.generators c' → 5 ≤ c'
    ) := by
  have hOriginalSpan := data.baseGeneratorCandidate_sympSpan
  have hDualSpan := data.symplecticDualData.baseGeneratorCandidate_sympSpan
  exact
    ⟨⟨by simpa [originalCode, data] using hOriginalSpan,
        originalCode_extendedCode,
        originalCodeWithDistance.hasDistance,
        originalCode.ebits_minimal.symm,
        ⟨originalReachability⟩,
        originalEbitLowerBound⟩,
      ⟨by simpa [dualCode, data] using hDualSpan,
        dualCode_extendedCode,
        dualCodeWithDistance.hasDistance,
        dualCode.ebits_minimal.symm,
        ⟨dualReachability⟩,
        dualEbitLowerBound⟩⟩

/- 最后确认本实例行空间与矩阵应用文件中候选 Pauli 生成元的辛张成空间一致。
-/
def candidateRowEquiv :
    Fin cssPauliCandidate.generatorsList.length ≃ Fin 10 :=
  (parityCheckCSSIndexEquiv parityCheckMatrix).trans finSumFinEquiv

theorem candidate_checkMatrix_eq :
    Matrix.reindex candidateRowEquiv (Equiv.refl (Fin 24))
        (NQubitPauliGroupElement.checkMatrix
          cssPauliCandidate.generatorsList) =
      matrix := by
  have h := cssPauliCandidate_checkMatrix_eq_symplecticMatrix
  ext i j
  have hij := congrArg
    (fun M => M (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) h
  simpa [candidateRowEquiv, matrix, Matrix.reindex_apply] using hij

private theorem matrix_row_eq_candidateRow (i : Fin 10) :
    matrix.row i =
      (NQubitPauliGroupElement.checkMatrix
        cssPauliCandidate.generatorsList).row (candidateRowEquiv.symm i) := by
  funext j
  have hij := congrArg (fun M => M i j) candidate_checkMatrix_eq
  simpa [Matrix.reindex_apply] using hij.symm

theorem candidate_rowSpace_eq :
    Submodule.span (ZMod 2)
        (Set.range
          (NQubitPauliGroupElement.checkMatrix
            cssPauliCandidate.generatorsList).row) =
      space := by
  change Submodule.span (ZMod 2)
      (Set.range
        (NQubitPauliGroupElement.checkMatrix
          cssPauliCandidate.generatorsList).row) =
    Submodule.span (ZMod 2) (Set.range matrix.row)
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨candidateRowEquiv i, ?_⟩
    rw [matrix_row_eq_candidateRow]
    simp
  · rintro ⟨i, rfl⟩
    refine ⟨candidateRowEquiv.symm i, ?_⟩
    exact (matrix_row_eq_candidateRow i).symm

end Quantum.Kim2023BinaryExample
