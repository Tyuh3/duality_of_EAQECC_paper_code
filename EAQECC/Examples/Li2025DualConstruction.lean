import EAQECC.Minimality
import EAQECC.Quaternary.LinearCode
import EAQECC.Symplectic.EACode

/-!
Li 四元码实例。由具体生成矩阵证明迹类型、根空间及两侧最小重量，
再调用一般模型构造参数 [[6,3,2;1]] 与 [[6,1,5;3]] 的纠缠辅助对偶码。
-/

namespace Quantum.Li2025DualConstruction

open Quaternary

noncomputable local instance : Fintype QuaternaryField :=
  Fintype.ofFinite QuaternaryField

/- 文献中的两个四元生成向量。
-/
noncomputable def firstGenerator : QuaternaryVector 6 :=
  ![1, 1, 1, 1, 0, 0]

noncomputable def secondGenerator : QuaternaryVector 6 :=
  ![0, 1, omega, varpi, 1, 1]

/-- Li 四元生成矩阵。由两个长度为 6 的四元向量组成，
后续证明行线性无关，并以其四元行张成空间定义维数为 2 的线性码。
-/
noncomputable def liGeneratorMatrix :
    Matrix (Fin 2) (Fin 6) QuaternaryField :=
  ![firstGenerator, secondGenerator]

@[simp] private theorem generatorMatrix_row_zero :
    liGeneratorMatrix.row 0 = firstGenerator := by
  rfl

@[simp] private theorem generatorMatrix_row_one :
    liGeneratorMatrix.row 1 = secondGenerator := by
  rfl

private theorem generatorRows_linearIndependent :
    LinearIndependent QuaternaryField liGeneratorMatrix.row := by
  rw [linearIndependent_fin2]
  constructor
  · intro hZero
    have hCoordinate := congrFun hZero 4
    simp [liGeneratorMatrix, secondGenerator] at hCoordinate
  · intro a hMultiple
    have hCoordinate := congrFun hMultiple 0
    simp [liGeneratorMatrix, firstGenerator, secondGenerator] at hCoordinate

noncomputable def linearCode : QuaternaryLinearCode 6 :=
  Submodule.span QuaternaryField (Set.range liGeneratorMatrix.row)

theorem linearCode_finrank :
    Module.finrank QuaternaryField linearCode = 2 := by
  let b : Module.Basis (Fin 2) QuaternaryField linearCode :=
    Module.Basis.span generatorRows_linearIndependent
  simpa using Module.finrank_eq_card_basis b

/- 用两个四元系数表示全部码字；再将生成行展开为四个二元线性无关的加性生成行。
-/
private noncomputable def codeword
    (a b : QuaternaryField) : QuaternaryVector 6 :=
  a • firstGenerator + b • secondGenerator

private theorem codeword_mem
    (a b : QuaternaryField) : codeword a b ∈ linearCode := by
  apply linearCode.add_mem
  · exact linearCode.smul_mem a
      (Submodule.subset_span (Set.mem_range_self (0 : Fin 2)))
  · exact linearCode.smul_mem b
      (Submodule.subset_span (Set.mem_range_self (1 : Fin 2)))

noncomputable def additiveGeneratorMatrix :
    Matrix (Fin 4) (Fin 6) QuaternaryField :=
  ![omega • firstGenerator, omega • secondGenerator,
    varpi • firstGenerator, varpi • secondGenerator]

private theorem additiveGeneratorRows_linearIndependent :
    LinearIndependent (ZMod 2) additiveGeneratorMatrix.row := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients hCombination i
  have hAtZero := congrFun hCombination 0
  have hAtFour := congrFun hCombination 4
  simp only [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at hAtZero hAtFour
  dsimp [additiveGeneratorMatrix, firstGenerator, secondGenerator] at hAtZero hAtFour
  simp only [Pi.smul_apply, mul_one, mul_zero, smul_zero, add_zero,
    zero_add] at hAtZero hAtFour
  simp at hAtZero hAtFour
  change coefficients 0 • omega + coefficients 2 • varpi = 0 at hAtZero
  change coefficients 1 • omega + coefficients 3 • varpi = 0 at hAtFour
  have hZeroCoordinates := congrArg paperCoordinateEquiv hAtZero
  have hFourCoordinates := congrArg paperCoordinateEquiv hAtFour
  rw [map_zero, paperCoordinateEquiv_apply_combination] at hZeroCoordinates
  rw [map_zero, paperCoordinateEquiv_apply_combination] at hFourCoordinates
  fin_cases i
  · simpa using congrFun hZeroCoordinates 0
  · simpa using congrFun hFourCoordinates 0
  · simpa using congrFun hZeroCoordinates 1
  · simpa using congrFun hFourCoordinates 1

private theorem additiveRowSpace_eq :
    quaternaryMatrixRowSpace additiveGeneratorMatrix =
      linearCode.toAdditiveCode := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro u ⟨i, rfl⟩
    change additiveGeneratorMatrix.row i ∈ linearCode
    fin_cases i
    · exact linearCode.smul_mem omega
        (Submodule.subset_span (Set.mem_range_self (0 : Fin 2)))
    · exact linearCode.smul_mem omega
        (Submodule.subset_span (Set.mem_range_self (1 : Fin 2)))
    · exact linearCode.smul_mem varpi
        (Submodule.subset_span (Set.mem_range_self (0 : Fin 2)))
    · exact linearCode.smul_mem varpi
        (Submodule.subset_span (Set.mem_range_self (1 : Fin 2)))
  · let b : Module.Basis (Fin 4) (ZMod 2)
        (quaternaryMatrixRowSpace additiveGeneratorMatrix) :=
      Module.Basis.span additiveGeneratorRows_linearIndependent
    calc
      Module.finrank (ZMod 2)
          (quaternaryMatrixRowSpace additiveGeneratorMatrix) = 4 := by
        simpa using Module.finrank_eq_card_basis b
      _ = Module.finrank (ZMod 2) linearCode.toAdditiveCode := by
        rw [QuaternaryLinearCode.finrank_toAdditiveCode, linearCode_finrank]

/- 加性生成行的迹内积矩阵。矩阵等式包含 Lean 内部的有限判定，随后用独立行证明秩为 2。
该有限判定通过原生计算公理纳入证明，其计算部分依赖 Lean 编译器及运行时的正确性。
-/
private def expectedTraceGram : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![![0, 0, 0, 0],
    ![0, 0, 0, 1],
    ![0, 0, 0, 0],
    ![0, 1, 0, 0]]

private theorem traceGramMatrix_eq :
    traceGramMatrix additiveGeneratorMatrix = expectedTraceGram := by
  have hOmega : omega * (1 + omega) = 1 := by
    rw [← varpi_eq_one_add_omega, omega_mul_varpi]
  have hVarpi : varpi * (1 + omega) = omega := by
    rw [← varpi_eq_one_add_omega, varpi_mul_varpi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceGramMatrix, additiveGeneratorMatrix, firstGenerator,
      secondGenerator, traceInner, expectedTraceGram, Fin.sum_univ_succ,
      hOmega, hVarpi] <;> native_decide

private def traceGramBasisRows : Fin 2 → (Fin 4 → ZMod 2) :=
  ![expectedTraceGram.row 1, expectedTraceGram.row 3]

private theorem traceGramBasisRows_linearIndependent :
    LinearIndependent (ZMod 2) traceGramBasisRows := by
  rw [linearIndependent_fin2]
  constructor
  · intro hZero
    have hCoordinate := congrFun hZero 1
    simp [traceGramBasisRows, expectedTraceGram] at hCoordinate
  · intro a hMultiple
    have hCoordinate := congrFun hMultiple 3
    simp [traceGramBasisRows, expectedTraceGram] at hCoordinate

private theorem expectedTraceGram_rank :
    Matrix.rank expectedTraceGram = 2 := by
  rw [Matrix.rank_eq_finrank_span_row]
  have hSpan :
      Submodule.span (ZMod 2) (Set.range expectedTraceGram.row) =
        Submodule.span (ZMod 2) (Set.range traceGramBasisRows) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      fin_cases i
      · change expectedTraceGram.row (0 : Fin 4) ∈ _
        rw [show expectedTraceGram.row 0 = 0 by
          ext j
          fin_cases j <;> rfl]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span
          (Set.mem_range_self (0 : Fin 2))
      · change expectedTraceGram.row (2 : Fin 4) ∈ _
        rw [show expectedTraceGram.row 2 = 0 by
          ext j
          fin_cases j <;> rfl]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span
          (Set.mem_range_self (1 : Fin 2))
    · apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      fin_cases i
      · exact Submodule.subset_span
          (Set.mem_range_self (1 : Fin 4))
      · exact Submodule.subset_span
          (Set.mem_range_self (3 : Fin 4))
  rw [hSpan]
  let b : Module.Basis (Fin 2) (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range traceGramBasisRows)) :=
    Module.Basis.span traceGramBasisRows_linearIndependent
  simpa using Module.finrank_eq_card_basis b

/-- Li 加性码的迹类型 [4,1]ₜ。
结合加性生成行的二元线性无关性与迹内积矩阵秩为 2，调用一般矩阵判定得到类型结论。
-/
theorem hasTraceType :
    linearCode.toAdditiveCode.HasTraceType 4 1 := by
  rw [← additiveRowSpace_eq]
  apply (quaternaryMatrixRowSpace_hasTraceType_iff
    additiveGeneratorMatrix additiveGeneratorRows_linearIndependent).mpr
  rw [traceGramMatrix_eq, expectedTraceGram_rank]

/- 以下在 Lean 中按四元系数分类计算码字坐标与重量，
得到零码字、第二个系数为零的非零码字重量为 4、其余码字重量为 5。
-/
private theorem quaternaryField_cases (a : QuaternaryField) :
    a = 0 ∨ a = 1 ∨ a = omega ∨ a = varpi := by
  classical
  generalize hx : paperCoordinateEquiv a 0 = x
  generalize hz : paperCoordinateEquiv a 1 = z
  have h := eq_paper_combination a
  rw [hx, hz] at h
  have hOmegaVarpi : omega + varpi = 1 := by
    rw [varpi_eq_one_add_omega]
    simpa [add_assoc, add_comm] using CharTwo.add_cancel_left omega 1
  have binaryCases (t : ZMod 2) : t = 0 ∨ t = 1 := by
    by_cases ht : t = 0
    · exact Or.inl ht
    · right
      apply ZMod.val_injective 2
      rw [ZMod.val_one 2]
      have hval : t.val ≠ 0 := by
        intro hzero
        exact ht ((ZMod.val_eq_zero t).mp hzero)
      have hlt := t.val_lt
      omega
  rcases binaryCases x with rfl | rfl <;>
    rcases binaryCases z with rfl | rfl
  · exact Or.inl (by simpa using h)
  · exact Or.inr (Or.inr (Or.inr
      (by simpa only [zero_smul, one_smul, zero_add] using h)))
  · exact Or.inr (Or.inr (Or.inl
      (by simpa only [zero_smul, one_smul, add_zero] using h)))
  · have hValue : a = omega + varpi := by
      simpa only [one_smul] using h
    exact Or.inr (Or.inl (hValue.trans hOmegaVarpi))

private theorem codeword_eq_vector (a b : QuaternaryField) :
    codeword a b = ![a, a + b, a + b * omega,
      a + b * varpi, b, b] := by
  ext i
  fin_cases i <;>
    simp [codeword, firstGenerator, secondGenerator]

private theorem exists_codeword_coefficients
    {u : QuaternaryVector 6} (hu : u ∈ linearCode) :
    ∃ a b : QuaternaryField, u = codeword a b := by
  let basis : Module.Basis (Fin 2) QuaternaryField linearCode :=
    Module.Basis.span generatorRows_linearIndependent
  let uCode : linearCode := ⟨u, hu⟩
  let coordinates := basis.repr uCode
  refine ⟨coordinates 0, coordinates 1, ?_⟩
  have hReconstruct := basis.sum_repr uCode
  have hAmbient := congrArg linearCode.subtype hReconstruct
  have hBasisZero : linearCode.subtype (basis 0) = firstGenerator := by
    exact Module.Basis.coe_span_apply generatorRows_linearIndependent 0
  have hBasisOne : linearCode.subtype (basis 1) = secondGenerator := by
    exact Module.Basis.coe_span_apply generatorRows_linearIndependent 1
  change u = codeword (coordinates 0) (coordinates 1)
  symm
  rw [Fin.sum_univ_two, map_add, map_smul, map_smul,
    hBasisZero, hBasisOne] at hAmbient
  exact hAmbient

@[simp] private theorem one_add_omega :
    (1 : QuaternaryField) + omega = varpi :=
  varpi_eq_one_add_omega.symm

@[simp] private theorem omega_add_one :
    omega + (1 : QuaternaryField) = varpi := by
  rw [add_comm, one_add_omega]

@[simp] private theorem omega_add_varpi : omega + varpi = 1 := by
  rw [varpi_eq_one_add_omega]
  simpa [add_assoc, add_comm] using CharTwo.add_cancel_left omega 1

@[simp] private theorem varpi_add_omega : varpi + omega = 1 := by
  rw [add_comm, omega_add_varpi]

@[simp] private theorem one_add_varpi :
    (1 : QuaternaryField) + varpi = omega := by
  rw [varpi_eq_one_add_omega]
  simpa [add_assoc] using CharTwo.add_cancel_left 1 omega

@[simp] private theorem varpi_add_one :
    varpi + (1 : QuaternaryField) = omega := by
  rw [add_comm, one_add_varpi]

private theorem hammingWeight_eq_five_of_unique_zero
    (u : QuaternaryVector 6) (zeroIndex : Fin 6)
    (hZero : u zeroIndex = 0)
    (hUnique : ∀ i, u i = 0 → i = zeroIndex) :
    hammingWeight u = 5 := by
  have hSupport : hammingSupport u = Finset.univ.erase zeroIndex := by
    ext i
    simp only [mem_hammingSupport_iff, Finset.mem_erase,
      Finset.mem_univ, and_true]
    constructor
    · intro hi hEq
      subst i
      exact hi hZero
    · intro hi hValue
      exact hi (hUnique i hValue)
  rw [hammingWeight, hSupport, Finset.card_erase_of_mem]
  · decide
  · exact Finset.mem_univ zeroIndex

private theorem hammingWeight_codeword_zero_right
    (a : QuaternaryField) (ha : a ≠ 0) :
    hammingWeight (codeword a 0) = 4 := by
  have hSupport : hammingSupport (codeword a 0) =
      ({0, 1, 2, 3} : Finset (Fin 6)) := by
    ext i
    fin_cases i <;>
      simp [hammingSupport, codeword_eq_vector, ha]
  rw [hammingWeight, hSupport]
  decide

set_option maxHeartbeats 1000000 in

private theorem hammingWeight_codeword_of_second_ne_zero
    (a b : QuaternaryField) (hb : b ≠ 0) :
    hammingWeight (codeword a b) = 5 := by
  have proveAt (x y : QuaternaryField) (i₀ : Fin 6)
      (hz : codeword x y i₀ = 0)
      (hu : ∀ i, codeword x y i = 0 → i = i₀) :
      hammingWeight (codeword x y) = 5 :=
    hammingWeight_eq_five_of_unique_zero _ i₀ hz hu
  rcases quaternaryField_cases a with ha | ha | ha | ha <;> subst a
  · rcases quaternaryField_cases b with hb₀ | hb₁ | hbω | hbϖ
    · exact (hb hb₀).elim
    · subst b
      apply proveAt 0 1 0
      · simp [codeword_eq_vector]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          omega_ne_zero, varpi_ne_zero]
    · subst b
      apply proveAt 0 omega 0
      · simp [codeword_eq_vector]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          omega_ne_zero, varpi_ne_zero]
    · subst b
      apply proveAt 0 varpi 0
      · simp [codeword_eq_vector]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          omega_ne_zero, varpi_ne_zero]
  · rcases quaternaryField_cases b with hb₀ | hb₁ | hbω | hbϖ
    · exact (hb hb₀).elim
    · subst b
      apply proveAt 1 1 1
      · simp [codeword_eq_vector, CharTwo.add_self_eq_zero]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          CharTwo.add_self_eq_zero, omega_ne_zero, varpi_ne_zero]
    · subst b
      apply proveAt 1 omega 3
      · simp [codeword_eq_vector, CharTwo.add_self_eq_zero]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          CharTwo.add_self_eq_zero, omega_ne_zero, varpi_ne_zero]
    · subst b
      apply proveAt 1 varpi 2
      · simp [codeword_eq_vector, CharTwo.add_self_eq_zero]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          CharTwo.add_self_eq_zero, omega_ne_zero, varpi_ne_zero]
  · rcases quaternaryField_cases b with hb₀ | hb₁ | hbω | hbϖ
    · exact (hb hb₀).elim
    · subst b
      apply proveAt omega 1 2
      · simp [codeword_eq_vector, CharTwo.add_self_eq_zero]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          CharTwo.add_self_eq_zero, omega_ne_zero, varpi_ne_zero]
    · subst b
      apply proveAt omega omega 1
      · simp [codeword_eq_vector, CharTwo.add_self_eq_zero]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          CharTwo.add_self_eq_zero, omega_ne_zero, varpi_ne_zero]
    · subst b
      apply proveAt omega varpi 3
      · simp [codeword_eq_vector, CharTwo.add_self_eq_zero]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          CharTwo.add_self_eq_zero, omega_ne_zero, varpi_ne_zero]
  · rcases quaternaryField_cases b with hb₀ | hb₁ | hbω | hbϖ
    · exact (hb hb₀).elim
    · subst b
      apply proveAt varpi 1 3
      · simp [codeword_eq_vector, CharTwo.add_self_eq_zero]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          CharTwo.add_self_eq_zero, omega_ne_zero, varpi_ne_zero]
    · subst b
      apply proveAt varpi omega 2
      · simp [codeword_eq_vector, CharTwo.add_self_eq_zero]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          CharTwo.add_self_eq_zero, omega_ne_zero, varpi_ne_zero]
    · subst b
      apply proveAt varpi varpi 1
      · simp [codeword_eq_vector, CharTwo.add_self_eq_zero]
      · intro i hi
        fin_cases i <;> simp_all [codeword_eq_vector,
          CharTwo.add_self_eq_zero, omega_ne_zero, varpi_ne_zero]

private theorem codeword_eq_zero_iff (a b : QuaternaryField) :
    codeword a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro hZero
    have hAtZero := congrFun hZero 0
    have hAtFour := congrFun hZero 4
    constructor
    · simpa [codeword_eq_vector] using hAtZero
    · simpa [codeword_eq_vector] using hAtFour
  · rintro ⟨rfl, rfl⟩
    simp [codeword]

theorem linearCode_minimumDistance :
    HasMinimumHammingWeightOutside linearCode.toAdditiveCode ⊥ 4 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro u huCode huNonzero
    obtain ⟨a, b, rfl⟩ :=
      exists_codeword_coefficients
        ((QuaternaryLinearCode.mem_toAdditiveCode_iff linearCode u).mp huCode)
    by_cases hb : b = 0
    · subst b
      have ha : a ≠ 0 := by
        intro ha
        subst a
        apply huNonzero
        simp [codeword]
      rw [hammingWeight_codeword_zero_right a ha]
    · rw [hammingWeight_codeword_of_second_ne_zero a b hb]
      decide
  · refine ⟨codeword 1 0, ?_, ?_, ?_⟩
    · exact (QuaternaryLinearCode.mem_toAdditiveCode_iff
        linearCode (codeword 1 0)).mpr (codeword_mem 1 0)
    · simp [codeword_eq_zero_iff]
    · exact hammingWeight_codeword_zero_right 1 one_ne_zero

/- 由第一个生成向量张成的四元线性子码。以下证明它对应整个加性码的迹根空间，二元维数为 2。
-/
noncomputable def radicalCode : QuaternaryLinearCode 6 :=
  Submodule.span QuaternaryField
    (Set.range (fun _ : Fin 1 ↦ firstGenerator))

private theorem firstGenerator_linearIndependent :
    LinearIndependent QuaternaryField
      (fun _ : Fin 1 ↦ firstGenerator) := by
  rw [linearIndependent_unique_iff]
  intro hZero
  have hAtZero := congrFun hZero 0
  simp [firstGenerator] at hAtZero

private theorem radicalCode_finrank :
    Module.finrank QuaternaryField radicalCode = 1 := by
  let b : Module.Basis (Fin 1) QuaternaryField radicalCode :=
    Module.Basis.span firstGenerator_linearIndependent
  simpa using Module.finrank_eq_card_basis b

set_option maxHeartbeats 1000000 in

private theorem traceInner_codeword_zero_right
    (a b d : QuaternaryField) :
    traceInner (codeword a 0) (codeword b d) = 0 := by
  let ax := paperCoordinateEquiv a 0
  let az := paperCoordinateEquiv a 1
  let bx := paperCoordinateEquiv b 0
  let bz := paperCoordinateEquiv b 1
  let dx := paperCoordinateEquiv d 0
  let dz := paperCoordinateEquiv d 1
  have haCoeff : a = ax • omega + az • varpi :=
    eq_paper_combination a
  have hbCoeff : b = bx • omega + bz • varpi :=
    eq_paper_combination b
  have hdCoeff : d = dx • omega + dz • varpi :=
    eq_paper_combination d
  have haVector :
      codeword a 0 =
        ax • additiveGeneratorMatrix.row 0 +
          az • additiveGeneratorMatrix.row 2 := by
    ext i
    fin_cases i <;>
      simp [codeword_eq_vector, additiveGeneratorMatrix,
        firstGenerator, secondGenerator, haCoeff]
  have hbdVector :
      codeword b d =
        bx • additiveGeneratorMatrix.row 0 +
          dx • additiveGeneratorMatrix.row 1 +
          bz • additiveGeneratorMatrix.row 2 +
          dz • additiveGeneratorMatrix.row 3 := by
    ext i
    fin_cases i <;>
      simp [codeword_eq_vector, additiveGeneratorMatrix,
        firstGenerator, secondGenerator, hbCoeff, hdCoeff,
        add_mul, omega_mul_omega, omega_mul_varpi,
        varpi_mul_omega, varpi_mul_varpi,
        add_assoc, add_comm]
  have hGram (i j : Fin 4) :
      traceInner (additiveGeneratorMatrix.row i)
          (additiveGeneratorMatrix.row j) = expectedTraceGram i j := by
    have hEntry := congrArg (fun M ↦ M i j) traceGramMatrix_eq
    exact hEntry
  rw [haVector, hbdVector]
  simp only [traceInner_add_left, traceInner_add_right,
    traceInner_smul_left, traceInner_smul_right]
  rw [hGram 0 0, hGram 0 1, hGram 0 2, hGram 0 3,
    hGram 2 0, hGram 2 1, hGram 2 2, hGram 2 3]
  simp [expectedTraceGram]

private theorem exists_radicalCode_coefficient
    {u : QuaternaryVector 6} (hu : u ∈ radicalCode) :
    ∃ a : QuaternaryField, u = codeword a 0 := by
  have hRange :
      Set.range (fun _ : Fin 1 ↦ firstGenerator) = {firstGenerator} := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      simp
    · intro hv
      simp only [Set.mem_singleton_iff] at hv
      subst v
      exact ⟨0, rfl⟩
  rw [radicalCode, hRange, Submodule.mem_span_singleton] at hu
  obtain ⟨a, hScalar⟩ := hu
  exact ⟨a, by simpa [codeword] using hScalar.symm⟩

private theorem radicalCode_le_traceRadical :
    radicalCode.toAdditiveCode ≤
      traceRadical linearCode.toAdditiveCode := by
  intro u hu
  have huLinear :=
    (QuaternaryLinearCode.mem_toAdditiveCode_iff radicalCode u).mp hu
  obtain ⟨a, rfl⟩ := exists_radicalCode_coefficient huLinear
  rw [mem_traceRadical_iff]
  constructor
  · exact (QuaternaryLinearCode.mem_toAdditiveCode_iff
      linearCode (codeword a 0)).mpr (codeword_mem a 0)
  · rw [mem_traceOrthogonal_iff]
    intro v hv
    have hvLinear :=
      (QuaternaryLinearCode.mem_toAdditiveCode_iff linearCode v).mp hv
    obtain ⟨b, d, rfl⟩ := exists_codeword_coefficients hvLinear
    exact traceInner_codeword_zero_right a b d

theorem traceRadical_eq :
    traceRadical linearCode.toAdditiveCode =
      radicalCode.toAdditiveCode := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq radicalCode_le_traceRadical
  have hRadical :=
    QuaternaryAdditiveCode.radicalFinrank_add_two_mul_eq_of_hasTraceType
      hasTraceType
  calc
    Module.finrank (ZMod 2) radicalCode.toAdditiveCode = 2 := by
      rw [QuaternaryLinearCode.finrank_toAdditiveCode, radicalCode_finrank]
    _ = Module.finrank (ZMod 2)
        (traceRadical linearCode.toAdditiveCode) := by
      omega

theorem traceRadical_finrank :
    Module.finrank (ZMod 2)
      (traceRadical linearCode.toAdditiveCode) = 2 := by
  rw [traceRadical_eq,
    QuaternaryLinearCode.finrank_toAdditiveCode, radicalCode_finrank]

private theorem codeword_mem_traceRadical_iff
    (a b : QuaternaryField) :
    codeword a b ∈ traceRadical linearCode.toAdditiveCode ↔ b = 0 := by
  constructor
  · intro hRadical
    rw [traceRadical_eq] at hRadical
    have hLinear :=
      (QuaternaryLinearCode.mem_toAdditiveCode_iff
        radicalCode (codeword a b)).mp hRadical
    obtain ⟨r, hRepresentation⟩ :=
      exists_radicalCode_coefficient hLinear
    have hAtFour := congrFun hRepresentation 4
    simpa [codeword_eq_vector] using hAtFour
  · intro hb
    subst b
    rw [traceRadical_eq]
    apply (QuaternaryLinearCode.mem_toAdditiveCode_iff
      radicalCode (codeword a 0)).mpr
    have hGenerator : firstGenerator ∈ radicalCode :=
      Submodule.subset_span (Set.mem_range_self (0 : Fin 1))
    simpa [codeword] using radicalCode.smul_mem a hGenerator

/-- 对偶侧最小重量为 5。迹根空间恰对应第二个系数为零的码字，
排除这些码字后其余码字重量均为 5，并给出达到该重量的码字。
-/
theorem dualDistance :
    HasMinimumHammingWeightOutside linearCode.toAdditiveCode
      (traceRadical linearCode.toAdditiveCode) 5 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro u huCode huRadical
    have huLinear :=
      (QuaternaryLinearCode.mem_toAdditiveCode_iff linearCode u).mp huCode
    obtain ⟨a, b, rfl⟩ := exists_codeword_coefficients huLinear
    have hb : b ≠ 0 := by
      intro hb
      exact huRadical ((codeword_mem_traceRadical_iff a b).mpr hb)
    rw [hammingWeight_codeword_of_second_ne_zero a b hb]
  · refine ⟨codeword 0 1, ?_, ?_, ?_⟩
    · exact (QuaternaryLinearCode.mem_toAdditiveCode_iff
        linearCode (codeword 0 1)).mpr (codeword_mem 0 1)
    · exact fun hRadical ↦ one_ne_zero
        ((codeword_mem_traceRadical_iff 0 1).mp hRadical)
    · exact hammingWeight_codeword_of_second_ne_zero 0 1 one_ne_zero

/- 为原码侧距离准备逐坐标取值的码字，证明迹对偶中不存在重量为 1 的非零向量。
-/
private noncomputable def coordinateCodeword
    (j : Fin 6) (a : QuaternaryField) : QuaternaryVector 6 :=
  if (j : ℕ) < 4 then codeword a 0 else codeword 0 a

private theorem coordinateCodeword_mem
    (j : Fin 6) (a : QuaternaryField) :
    coordinateCodeword j a ∈ linearCode.toAdditiveCode := by
  apply (QuaternaryLinearCode.mem_toAdditiveCode_iff
    linearCode (coordinateCodeword j a)).mpr
  fin_cases j <;> simp [coordinateCodeword, codeword_mem]

@[simp] private theorem coordinateCodeword_apply_self
    (j : Fin 6) (a : QuaternaryField) :
    coordinateCodeword j a j = a := by
  fin_cases j <;> simp [coordinateCodeword, codeword_eq_vector]

private theorem exists_hammingSupport_singleton_of_weight_one
    (u : QuaternaryVector 6) (hWeight : hammingWeight u = 1) :
    ∃ j : Fin 6, hammingSupport u = {j} := by
  exact Finset.card_eq_one.mp hWeight

private theorem traceInner_eq_of_hammingSupport_eq_singleton
    (u v : QuaternaryVector 6) (j : Fin 6)
    (hSupport : hammingSupport u = {j}) :
    traceInner u v = fieldTrace (u j * conjugation (v j)) := by
  unfold traceInner
  apply Finset.sum_eq_single j
  · intro i _ hij
    have hui : u i = 0 := by
      by_contra hi
      have hiSupport : i ∈ hammingSupport u :=
        (mem_hammingSupport_iff u i).mpr hi
      rw [hSupport, Finset.mem_singleton] at hiSupport
      exact hij hiSupport
    simp [hui]
  · simp

private theorem noWeightOneInTraceDual
    (u : QuaternaryVector 6)
    (huDual : u ∈ traceOrthogonal linearCode.toAdditiveCode) :
    hammingWeight u ≠ 1 := by
  intro hWeight
  obtain ⟨j, hSupport⟩ :=
    exists_hammingSupport_singleton_of_weight_one u hWeight
  have huj : u j ≠ 0 := by
    have hjSupport : j ∈ hammingSupport u := by
      rw [hSupport]
      simp
    exact (mem_hammingSupport_iff u j).mp hjSupport
  rw [mem_traceOrthogonal_iff] at huDual
  have contradictWith (v : QuaternaryVector 6)
      (hvCode : v ∈ linearCode.toAdditiveCode)
      (hPairing : fieldTrace (u j * conjugation (v j)) ≠ 0) : False := by
    have hOrthogonal := huDual v hvCode
    rw [traceInner_eq_of_hammingSupport_eq_singleton u v j hSupport]
      at hOrthogonal
    exact hPairing hOrthogonal
  rcases quaternaryField_cases (u j) with hZero | hOne | hOmega | hVarpi
  · exact huj hZero
  · apply contradictWith (coordinateCodeword j omega)
      (coordinateCodeword_mem j omega)
    simp [hOne]
  · apply contradictWith (coordinateCodeword j varpi)
      (coordinateCodeword_mem j varpi)
    simp [hOmega]
  · apply contradictWith (coordinateCodeword j omega)
      (coordinateCodeword_mem j omega)
    simp [hVarpi]

noncomputable def originalWitness : QuaternaryVector 6 :=
  ![0, 0, 0, 0, 1, 1]

theorem originalWitness_spec :
    originalWitness ∈ traceOrthogonal linearCode.toAdditiveCode ∧
    originalWitness ∉ traceRadical linearCode.toAdditiveCode ∧
    hammingWeight originalWitness = 2 := by
  constructor
  · rw [mem_traceOrthogonal_iff]
    intro v hvCode
    have hvLinear :=
      (QuaternaryLinearCode.mem_toAdditiveCode_iff linearCode v).mp hvCode
    obtain ⟨a, b, rfl⟩ := exists_codeword_coefficients hvLinear
    simp [traceInner, originalWitness, codeword_eq_vector,
      Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  constructor
  · rw [traceRadical_eq]
    intro hRadical
    have hLinear :=
      (QuaternaryLinearCode.mem_toAdditiveCode_iff
        radicalCode originalWitness).mp hRadical
    obtain ⟨a, hRepresentation⟩ :=
      exists_radicalCode_coefficient hLinear
    have hAtFour := congrFun hRepresentation 4
    simp [originalWitness, codeword_eq_vector] at hAtFour
  · have hSupport :
        hammingSupport originalWitness = ({4, 5} : Finset (Fin 6)) := by
      ext i
      fin_cases i <;> simp [hammingSupport, originalWitness]
    rw [hammingWeight, hSupport]
    decide

/-- 原码侧最小重量为 2。在迹对偶中排除迹根空间后，
证明重量至少为 2，并给出重量为 2 且不属于根空间的向量。
-/
theorem originalDistance :
    HasMinimumHammingWeightOutside
      (traceOrthogonal linearCode.toAdditiveCode)
      (traceRadical linearCode.toAdditiveCode) 2 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro u huDual huRadical
    have huNeZero : u ≠ 0 := by
      intro huZero
      subst u
      exact huRadical (traceRadical linearCode.toAdditiveCode).zero_mem
    have hPositive : 0 < hammingWeight u :=
      (hammingWeight_pos_iff u).mpr huNeZero
    have hNotOne := noWeightOneInTraceDual u huDual
    omega
  · exact ⟨originalWitness, originalWitness_spec.1,
      originalWitness_spec.2.1, originalWitness_spec.2.2⟩

/- 由系数与码字的一一对应统计重量分布。以下分别计算整个线性码和迹根空间的重量枚举多项式。
-/
private theorem hammingWeight_codeword (a b : QuaternaryField) :
    hammingWeight (codeword a b) =
      if b = 0 then (if a = 0 then 0 else 4) else 5 := by
  by_cases hb : b = 0
  · subst b
    simp only [if_pos]
    by_cases ha : a = 0
    · subst a
      simp [codeword, hammingWeight_eq_zero_iff]
    · simp [ha, hammingWeight_codeword_zero_right]
  · simp [hb, hammingWeight_codeword_of_second_ne_zero]

private noncomputable def coefficientEquiv :
    (Fin 2 → QuaternaryField) ≃ₗ[QuaternaryField] linearCode :=
  (Module.Basis.span generatorRows_linearIndependent).equivFun.symm

private theorem coefficientEquiv_apply (x : Fin 2 → QuaternaryField) :
    ((coefficientEquiv x : linearCode) : QuaternaryVector 6) =
      codeword (x 0) (x 1) := by
  change linearCode.subtype (coefficientEquiv x) = _
  change linearCode.subtype
    ((Module.Basis.span generatorRows_linearIndependent).equivFun.symm x) = _
  have hExpansion :=
    (Module.Basis.span generatorRows_linearIndependent).equivFun_symm_apply x
  rw [hExpansion, Fin.sum_univ_two]
  change x 0 •
      (((Module.Basis.span generatorRows_linearIndependent) 0 : linearCode) :
        QuaternaryVector 6) +
      x 1 •
      (((Module.Basis.span generatorRows_linearIndependent) 1 : linearCode) :
        QuaternaryVector 6) = _
  rw [
    Module.Basis.coe_span_apply generatorRows_linearIndependent 0,
    Module.Basis.coe_span_apply generatorRows_linearIndependent 1]
  rfl

private def coefficientPairEquiv :
    (Fin 2 → QuaternaryField) ≃
      QuaternaryField × QuaternaryField where
  toFun x := (x 0, x 1)
  invFun p := ![p.1, p.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨a, b⟩
    rfl

private noncomputable def wordEquiv :
    QuaternaryField × QuaternaryField ≃
      linearCode.toAdditiveCode :=
  coefficientPairEquiv.symm.trans
    (coefficientEquiv.toEquiv.trans
      (linearCode.restrictScalarsEquiv (ZMod 2)).toEquiv.symm)

@[simp] private theorem wordEquiv_apply (a b : QuaternaryField) :
    ((wordEquiv (a, b) : linearCode.toAdditiveCode) :
        QuaternaryVector 6) = codeword a b := by
  change ((coefficientEquiv (![a, b] : Fin 2 → QuaternaryField) :
    linearCode) : QuaternaryVector 6) = codeword a b
  simpa using coefficientEquiv_apply (![a, b] : Fin 2 → QuaternaryField)

set_option maxHeartbeats 1000000 in

private theorem linearCode_enumerator_as_sum :
    QuaternaryAdditiveCode.hammingWeightEnumerator
        linearCode.toAdditiveCode =
      ∑ p : QuaternaryField × QuaternaryField,
        Polynomial.X ^ hammingWeight (codeword p.1 p.2) := by
  classical
  unfold QuaternaryAdditiveCode.hammingWeightEnumerator
  rw [← @Equiv.sum_comp
    (QuaternaryField × QuaternaryField)
    linearCode.toAdditiveCode (Polynomial ℕ)
    inferInstance (Fintype.ofFinite linearCode.toAdditiveCode)
    inferInstance wordEquiv
    (fun u : linearCode.toAdditiveCode ↦
      Polynomial.X ^ hammingWeight (u : QuaternaryVector 6))]
  apply Finset.sum_congr rfl
  intro p _
  rw [wordEquiv_apply]

private theorem quaternaryField_card :
    Fintype.card QuaternaryField = 4 := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_quaternaryField

private theorem sum_over_second_coefficient (a : QuaternaryField) :
    (∑ b : QuaternaryField,
      (Polynomial.X : Polynomial ℕ) ^ hammingWeight (codeword a b)) =
        (if a = 0 then 1 else
          (Polynomial.X : Polynomial ℕ) ^ 4) +
          3 * (Polynomial.X : Polynomial ℕ) ^ 5 := by
  classical
  let f : QuaternaryField → Polynomial ℕ := fun b ↦
    Polynomial.X ^ hammingWeight (codeword a b)
  have hNonzero :
      (∑ b ∈ Finset.univ.erase (0 : QuaternaryField), f b) =
        (Finset.univ.erase (0 : QuaternaryField)).card •
          (Polynomial.X ^ 5 : Polynomial ℕ) := by
    calc
      (∑ b ∈ Finset.univ.erase (0 : QuaternaryField), f b) =
          ∑ _b ∈ Finset.univ.erase (0 : QuaternaryField),
            (Polynomial.X ^ 5 : Polynomial ℕ) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hbZero : b ≠ 0 := (Finset.mem_erase.mp hb).1
        exact congrArg (fun w : ℕ ↦ Polynomial.X ^ w)
          (hammingWeight_codeword_of_second_ne_zero a b hbZero)
      _ = _ := Finset.sum_const _
  have hEraseCard :
      (Finset.univ.erase (0 : QuaternaryField)).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, quaternaryField_card]
  calc
    (∑ b : QuaternaryField,
        Polynomial.X ^ hammingWeight (codeword a b)) =
        (∑ b ∈ Finset.univ.erase (0 : QuaternaryField), f b) +
          f 0 := by
      exact (Finset.sum_erase_add Finset.univ f
        (Finset.mem_univ (0 : QuaternaryField))).symm
    _ = 3 • (Polynomial.X ^ 5 : Polynomial ℕ) + f 0 := by
      rw [hNonzero, hEraseCard]
    _ = (if a = 0 then 1 else Polynomial.X ^ 4) +
          3 * Polynomial.X ^ 5 := by
      unfold f
      rw [hammingWeight_codeword]
      by_cases ha : a = 0 <;> simp [ha]
      <;> ring

private theorem sum_if_zero (p q : Polynomial ℕ) :
    (∑ a : QuaternaryField, if a = 0 then p else q) =
      p + 3 * q := by
  classical
  let f : QuaternaryField → Polynomial ℕ := fun a ↦
    if a = 0 then p else q
  have hNonzero :
      (∑ a ∈ Finset.univ.erase (0 : QuaternaryField), f a) =
        3 • q := by
    calc
      (∑ a ∈ Finset.univ.erase (0 : QuaternaryField), f a) =
          ∑ _a ∈ Finset.univ.erase (0 : QuaternaryField), q := by
        apply Finset.sum_congr rfl
        intro a ha
        have haZero : a ≠ 0 := (Finset.mem_erase.mp ha).1
        simp [f, haZero]
      _ = (Finset.univ.erase (0 : QuaternaryField)).card • q :=
        Finset.sum_const _
      _ = 3 • q := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ 0),
          Finset.card_univ, quaternaryField_card]
  calc
    (∑ a : QuaternaryField, if a = 0 then p else q) =
        (∑ a ∈ Finset.univ.erase (0 : QuaternaryField), f a) +
          f 0 := by
      exact (Finset.sum_erase_add Finset.univ f
        (Finset.mem_univ (0 : QuaternaryField))).symm
    _ = 3 • q + p := by simp [hNonzero, f]
    _ = p + 3 * q := by
      simp [nsmul_eq_mul]
      ring

theorem linearCode_weightEnumerator :
    QuaternaryAdditiveCode.hammingWeightEnumerator
        linearCode.toAdditiveCode =
      1 + 3 * (Polynomial.X : Polynomial ℕ) ^ 4 +
        12 * (Polynomial.X : Polynomial ℕ) ^ 5 := by
  rw [linearCode_enumerator_as_sum, Fintype.sum_prod_type]
  simp_rw [sum_over_second_coefficient]
  rw [Finset.sum_add_distrib]
  rw [sum_if_zero]
  simp only [Finset.sum_const, Finset.card_univ, quaternaryField_card]
  simp [nsmul_eq_mul]
  ring

private noncomputable def radicalWordEquiv :
    QuaternaryField ≃ radicalCode.toAdditiveCode where
  toFun a := by
    refine ⟨codeword a 0, ?_⟩
    apply (QuaternaryLinearCode.mem_toAdditiveCode_iff
      radicalCode (codeword a 0)).mpr
    have hGenerator : firstGenerator ∈ radicalCode :=
      Submodule.subset_span (Set.mem_range_self (0 : Fin 1))
    simpa [codeword] using radicalCode.smul_mem a hGenerator
  invFun u := (u : QuaternaryVector 6) 0
  left_inv a := by
    simp [codeword_eq_vector]
  right_inv u := by
    apply Subtype.ext
    have huLinear :=
      (QuaternaryLinearCode.mem_toAdditiveCode_iff
        radicalCode (u : QuaternaryVector 6)).mp u.property
    obtain ⟨a, hRepresentation⟩ :=
      exists_radicalCode_coefficient huLinear
    have hAtZero : (u : QuaternaryVector 6) 0 = a := by
      have := congrFun hRepresentation 0
      simpa [codeword_eq_vector] using this
    change codeword ((u : QuaternaryVector 6) 0) 0 =
      (u : QuaternaryVector 6)
    rw [hAtZero]
    exact hRepresentation.symm

set_option maxHeartbeats 1000000 in

private theorem radicalCode_enumerator_as_sum :
    QuaternaryAdditiveCode.hammingWeightEnumerator
        radicalCode.toAdditiveCode =
      ∑ a : QuaternaryField,
        (Polynomial.X : Polynomial ℕ) ^
          hammingWeight (codeword a 0) := by
  classical
  unfold QuaternaryAdditiveCode.hammingWeightEnumerator
  rw [← @Equiv.sum_comp QuaternaryField
    radicalCode.toAdditiveCode (Polynomial ℕ)
    inferInstance (Fintype.ofFinite radicalCode.toAdditiveCode)
    inferInstance radicalWordEquiv
    (fun u : radicalCode.toAdditiveCode ↦
      Polynomial.X ^ hammingWeight (u : QuaternaryVector 6))]
  apply Finset.sum_congr rfl
  intro a _
  rfl

private theorem radicalCode_weightEnumerator :
    QuaternaryAdditiveCode.hammingWeightEnumerator
        radicalCode.toAdditiveCode =
      1 + 3 * (Polynomial.X : Polynomial ℕ) ^ 4 := by
  rw [radicalCode_enumerator_as_sum]
  calc
    (∑ a : QuaternaryField,
        (Polynomial.X : Polynomial ℕ) ^
          hammingWeight (codeword a 0)) =
        ∑ a : QuaternaryField,
          if a = 0 then 1 else
            (Polynomial.X : Polynomial ℕ) ^ 4 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hammingWeight_codeword]
      by_cases ha : a = 0 <;> simp [ha]
    _ = _ := sum_if_zero 1 ((Polynomial.X : Polynomial ℕ) ^ 4)

theorem traceRadical_weightEnumerator :
    QuaternaryAdditiveCode.hammingWeightEnumerator
        (traceRadical linearCode.toAdditiveCode) =
      1 + 3 * (Polynomial.X : Polynomial ℕ) ^ 4 := by
  rw [traceRadical_eq]
  exact radicalCode_weightEnumerator

/-- 将本实例的加性码、迹类型、根空间维数及参数组织为一般四元输入，
随后转换为二元辛输入，并调用一般构造得到原码和对偶码。
-/
noncomputable def additiveData : EAAdditiveCodeData 6 4 2 1 3 where
  additiveCode := linearCode.toAdditiveCode
  hasTraceType := hasTraceType
  radical_finrank := traceRadical_finrank
  parameter_eq := by decide

noncomputable def binarySpace : BinarySymplecticSubspace 6 :=
  quaternaryToBinarySubspace linearCode.toAdditiveCode

noncomputable def binaryData : EASymplecticData 6 4 2 1 3 :=
  additiveData.toEASymplecticData

@[simp]
theorem binaryData_stabilizerSpace :
    binaryData.stabilizerSpace = binarySpace := by
  rfl

noncomputable def originalCode : EACode 6 3 1 :=
  binaryData.toEACode

noncomputable def dualCode : EACode 6 1 3 :=
  binaryData.symplecticDualData.toEACode

@[simp]
theorem originalCode_extendedCode :
    originalCode.extendedCode = additiveData.toStabilizerCode := by
  rfl

@[simp]
theorem dualCode_extendedCode :
    dualCode.extendedCode = additiveData.toDualStabilizerCode := by
  rfl

/- 复用一般理论得到迹对偶类型及根空间保持关系。
-/
theorem traceDual_hasTraceType :
    (traceOrthogonal linearCode.toAdditiveCode).HasTraceType 8 3 := by
  simpa using
    QuaternaryAdditiveCode.traceOrthogonal_hasTraceType hasTraceType

theorem traceDual_radical :
    traceRadical (traceOrthogonal linearCode.toAdditiveCode) =
      traceRadical linearCode.toAdditiveCode := by
  exact traceRadical_traceOrthogonal linearCode.toAdditiveCode

/-- Li 实例的迹对偶与辛对偶对应。
把本实例的迹对偶转换为二元子空间，所得空间恰为原二元辛空间的辛对偶。
后续同样复用一般对应关系得到根空间与类型结论。
-/
theorem binaryTraceDual :
    quaternaryToBinarySubspace
        (traceOrthogonal linearCode.toAdditiveCode) =
      NQubitPauliGroupElement.sympOrthogonal binarySpace := by
  simpa [binarySpace] using
    quaternaryToBinarySubspace_traceOrthogonal
      linearCode.toAdditiveCode

theorem binaryRadical :
    quaternaryToBinarySubspace
        (traceRadical linearCode.toAdditiveCode) =
      symplecticRadical binarySpace := by
  simpa [binarySpace] using
    quaternaryToBinarySubspace_traceRadical linearCode.toAdditiveCode

theorem binarySpace_hasType :
    binarySpace.HasType 4 1 := by
  simpa using binaryData.hasType

theorem binaryRadical_finrank :
    Module.finrank (ZMod 2) (symplecticRadical binarySpace) = 2 := by
  simpa using binaryData.radical_finrank

theorem binaryDual_hasType :
    BinarySymplecticSubspace.HasType
      (NQubitPauliGroupElement.sympOrthogonal binarySpace) 8 3 := by
  simpa using binaryData.symplecticDual_hasType

theorem binaryDual_radical :
    symplecticRadical
        (NQubitPauliGroupElement.sympOrthogonal binarySpace) =
      symplecticRadical binarySpace := by
  exact BinarySymplecticSubspace.radical_sympOrthogonal binarySpace

/- 把本实例证明的最小重量代入完整四元对偶定理，得到发送端距离为 2 和 5 的两侧码。
-/
noncomputable def originalCodeWithDistance :
    EACodeWithDistance 6 3 2 1 where
  toEACode := originalCode
  hasDistance := by
    have hDistance :=
      additiveData.quaternaryEAQECCDuality_full.1.2.2.1 (by decide)
    obtain ⟨d, hCodeDistance, hMinimum⟩ := hDistance
    have hd : d = 2 := hMinimum.unique originalDistance
    subst d
    simpa using hCodeDistance

noncomputable def dualCodeWithDistance :
    EACodeWithDistance 6 1 5 3 where
  toEACode := dualCode
  hasDistance := by
    have hDistance :=
      additiveData.quaternaryEAQECCDuality_full.2.2.1 (by decide)
    obtain ⟨d, hCodeDistance, hMinimum⟩ := hDistance
    have hd : d = 5 := hMinimum.unique dualDistance
    subst d
    simpa using hCodeDistance

/-- Li 四元码的完整对偶实例。
以一般四元对偶定理为依据，结合本实例的距离证明，
得到 [[6,3,2;1]] 与 [[6,1,5;3]] 两侧码的参数、稳定子与发送端正规化子对应。
-/
theorem quaternaryEAQECCDualityInstance :
    (
      (3 = 6 + 1 - 4 ∧ 3 = 6 - 1 - 2) ∧
      originalCode.HasDistance 2 ∧
      HasMinimumHammingWeightOutside
        (traceOrthogonal linearCode.toAdditiveCode)
        (traceRadical linearCode.toAdditiveCode) 2 ∧
      IsAdditiveEAStabilizerOf
        linearCode.toAdditiveCode originalCode.extendedCode ∧
      IsAdditiveEANormalizerOf
        (traceOrthogonal linearCode.toAdditiveCode)
        originalCode.extendedCode
    ) ∧
    (
      (1 = 6 + 3 - 8 ∧ 1 = 6 - 3 - 2) ∧
      (traceOrthogonal linearCode.toAdditiveCode).HasTraceType 8 3 ∧
      dualCode.HasDistance 5 ∧
      HasMinimumHammingWeightOutside
        linearCode.toAdditiveCode
        (traceRadical linearCode.toAdditiveCode) 5 ∧
      IsAdditiveEAStabilizerOf
        (traceOrthogonal linearCode.toAdditiveCode)
        dualCode.extendedCode ∧
      IsAdditiveEANormalizerOf
        linearCode.toAdditiveCode dualCode.extendedCode
    ) := by
  obtain
    ⟨⟨hParameter, hAlternativeParameter, _, hOriginalStabilizer,
        hOriginalNormalizer⟩,
      ⟨hDualType, _, hDualStabilizer, hDualNormalizer⟩⟩ :=
    additiveData.quaternaryEAQECCDuality_full
  have hDualParameter : 1 = 6 + 3 - 8 := by
    exact binaryData.symplecticDualData.parameter_eq
  have hDualAlternative : 1 = 6 - 3 - 2 := by
    exact
      binaryData.symplecticDualData.logicalDimension_eq_length_sub_ebitCount_sub_radicalFinrank
  exact
    ⟨⟨⟨hParameter, hAlternativeParameter⟩,
        originalCodeWithDistance.hasDistance, originalDistance,
        by simpa using hOriginalStabilizer,
        by simpa using hOriginalNormalizer⟩,
      ⟨⟨hDualParameter, hDualAlternative⟩, hDualType,
        dualCodeWithDistance.hasDistance, dualDistance,
        by simpa using hDualStabilizer,
        by simpa using hDualNormalizer⟩⟩

/- 通过重量保持关系，将本实例的汉明距离转为辛重量距离，并给出同一实例的完整二元表述。
-/
private theorem originalSymplecticDistance :
    HasMinimumSymplecticWeightOutside
      (NQubitPauliGroupElement.sympOrthogonal binarySpace)
      (symplecticRadical binarySpace) 2 := by
  simpa [binarySpace] using
    (hasMinimumHammingWeight_traceOrthogonal_diff_traceRadical_iff
      linearCode.toAdditiveCode).mp originalDistance

private theorem dualSymplecticDistance :
    HasMinimumSymplecticWeightOutside binarySpace
      (symplecticRadical binarySpace) 5 := by
  simpa [binarySpace] using
    (hasMinimumHammingWeight_code_diff_traceRadical_iff
      linearCode.toAdditiveCode).mp dualDistance

theorem symplecticEAQECCDualityInstance :
    (
      (3 = 6 + 1 - 4 ∧ 3 = 6 - 1 - 2) ∧
      StabilizerGroup.StabilizerCode.HasBaseDistance
        (n := 6) (c := 1) originalCode.extendedCode 2 ∧
      HasMinimumSymplecticWeightOutside
        (NQubitPauliGroupElement.sympOrthogonal binarySpace)
        (symplecticRadical binarySpace) 2 ∧
      RealizesEAStabilizerSpace
        (NQubitPauliGroupElement.sympSpan
          originalCode.extendedCode.generatorsList)
        binarySpace ∧
      {v : BinarySymplecticVector 6 |
        binarySymplecticVectorToPauli (baseSymplecticEmbedding 6 1 v) ∈
          StabilizerGroup.pauliNormalizer
            originalCode.extendedCode.toStabilizerGroup} =
        (NQubitPauliGroupElement.sympOrthogonal binarySpace :
          Set (BinarySymplecticVector 6))
    ) ∧
    (
      BinarySymplecticSubspace.HasType
        (NQubitPauliGroupElement.sympOrthogonal binarySpace) 8 3 ∧
      StabilizerGroup.StabilizerCode.HasBaseDistance
        (n := 6) (c := 3) dualCode.extendedCode 5 ∧
      HasMinimumSymplecticWeightOutside binarySpace
        (symplecticRadical binarySpace) 5 ∧
      RealizesEAStabilizerSpace
        (NQubitPauliGroupElement.sympSpan
          dualCode.extendedCode.generatorsList)
        (NQubitPauliGroupElement.sympOrthogonal binarySpace) ∧
      {v : BinarySymplecticVector 6 |
        binarySymplecticVectorToPauli (baseSymplecticEmbedding 6 3 v) ∈
          StabilizerGroup.pauliNormalizer
            dualCode.extendedCode.toStabilizerGroup} =
        (binarySpace : Set (BinarySymplecticVector 6))
    ) := by
  have hSymplecticDuality := binaryData.symplecticEAQECCDuality_full
  obtain
    ⟨⟨hParameter, hAlternativeParameter, hOriginalDistance,
        hOriginalRealizes, hOriginalNormalizer⟩,
      ⟨hDualDistance, hDualRealizes, hDualNormalizer⟩⟩ := hSymplecticDuality
  obtain ⟨d, hOriginalCodeDistance, hOriginalMinimum⟩ :=
    hOriginalDistance (by decide)
  have hd : d = 2 := hOriginalMinimum.unique originalSymplecticDistance
  subst d
  obtain ⟨dDual, hDualCodeDistance, hDualMinimum⟩ :=
    hDualDistance (by decide)
  have hdDual : dDual = 5 :=
    hDualMinimum.unique dualSymplecticDistance
  subst dDual
  exact
    ⟨⟨⟨hParameter, hAlternativeParameter⟩,
        by simpa [originalCode] using hOriginalCodeDistance,
        originalSymplecticDistance,
        by simpa [originalCode] using hOriginalRealizes,
        by simpa [originalCode] using hOriginalNormalizer⟩,
      ⟨binaryDual_hasType,
        by simpa [dualCode] using hDualCodeDistance,
        dualSymplecticDistance,
        by simpa [dualCode] using hDualRealizes,
        by simpa [dualCode] using hDualNormalizer⟩⟩

/- 两侧码按指定纠缠数可构造；后续复用一般下界，证明固定候选生成元下的纠缠数分别不能少于 1 和 3。
-/
noncomputable def originalReachability :
    CanExtendWith originalCode.generators 1 :=
  binaryData.toEACode_canExtendWith

noncomputable def dualReachability :
    CanExtendWith dualCode.generators 3 :=
  binaryData.symplecticDualData.toEACode_canExtendWith

theorem originalEbitLowerBound (c' : ℕ)
    (hExtension : CanExtendWith originalCode.generators c') :
    1 ≤ c' :=
  originalCode.c_minimal hExtension

theorem dualEbitLowerBound (c' : ℕ)
    (hExtension : CanExtendWith dualCode.generators c') :
    3 ≤ c' :=
  dualCode.c_minimal hExtension

theorem dualConstruction :
    originalCodeWithDistance.toEACode = originalCode ∧
    dualCodeWithDistance.toEACode = dualCode ∧
    originalCode.extendedCode = additiveData.toStabilizerCode ∧
    dualCode.extendedCode = additiveData.toDualStabilizerCode ∧
    Nonempty (CanExtendWith originalCode.generators 1) ∧
    (∀ c' : ℕ, CanExtendWith originalCode.generators c' → 1 ≤ c') ∧
    Nonempty (CanExtendWith dualCode.generators 3) ∧
    (∀ c' : ℕ, CanExtendWith dualCode.generators c' → 3 ≤ c') := by
  exact ⟨rfl, rfl, originalCode_extendedCode, dualCode_extendedCode,
    ⟨originalReachability⟩, originalEbitLowerBound,
    ⟨dualReachability⟩, dualEbitLowerBound⟩

end Quantum.Li2025DualConstruction
