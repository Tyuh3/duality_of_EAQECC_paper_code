import EAQECC.Basic
import EAQECC.Minimality
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Prod

/-!
经典二元码的欧几里得交空间与纠缠参数。联系行空间、欧几里得对偶和行内积矩阵秩，
构造 CSS 候选生成元，并核验 Kim 实例所用的具体生成矩阵与校验矩阵。
-/

namespace Quantum

namespace BinaryEuclideanHull

/- 二元矩阵行空间、欧几里得内积及行空间与其欧几里得对偶的交空间。
以下用矩阵乘法的核刻画对偶，并由秩与核维数关系计算交空间维数。
-/
abbrev matrixRowSpace {r n : ℕ}
    (G : Matrix (Fin r) (Fin n) (ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.range G.vecMulLinear

abbrev euclideanBilinForm (n : ℕ) :
    LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) :=
  dotProductBilin (ZMod 2) (ZMod 2)

abbrev rowSpaceEuclideanRadical {r n : ℕ}
    (G : Matrix (Fin r) (Fin n) (ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  matrixRowSpace G ⊓
    (euclideanBilinForm n).orthogonal (matrixRowSpace G)

theorem euclideanOrthogonal_rowSpace_eq_ker_mulVecLin
    {r n : ℕ}
    (G : Matrix (Fin r) (Fin n) (ZMod 2)) :
    (euclideanBilinForm n).orthogonal (matrixRowSpace G) =
      LinearMap.ker G.mulVecLin := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker]
    funext i
    have hrow : G.row i ∈ matrixRowSpace G := by
      rw [matrixRowSpace, range_vecMulLinear]
      exact Submodule.subset_span (Set.mem_range_self i)
    have horth := hx (G.row i) hrow
    simpa [euclideanBilinForm, LinearMap.BilinForm.IsOrtho, Matrix.mulVec,
      dotProduct_comm] using horth
  · intro hx
    rw [LinearMap.mem_ker] at hx
    intro y hy
    rcases hy with ⟨a, rfl⟩
    change dotProduct (Matrix.vecMul a G) x = 0
    rw [← Matrix.dotProduct_mulVec]
    change G.mulVec x = 0 at hx
    rw [hx]
    simp

theorem gramRank_add_rowSpaceRadicalFinrank_eq_rank
    {r n : ℕ}
    (G : Matrix (Fin r) (Fin n) (ZMod 2)) :
    Matrix.rank (G * G.transpose) +
        Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) =
      Matrix.rank G := by
  let D := matrixRowSpace G
  let L := G.mulVecLin
  let restricted := L.domRestrict D

  have hrange :
      LinearMap.range (G * G.transpose).mulVecLin =
        LinearMap.range restricted := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨G.transpose.mulVecLin x, ?_⟩, ?_⟩
      · change G.transpose.mulVecLin x ∈ matrixRowSpace G
        rw [Matrix.mulVecLin_transpose]
        exact ⟨x, rfl⟩
      · simp [restricted, L, Matrix.mulVecLin_mul]
    · rintro ⟨⟨z, hz⟩, rfl⟩
      rcases hz with ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      simp [restricted, L, Matrix.mulVecLin_mul]

  have hkernelMap :
      (LinearMap.ker restricted).map D.subtype =
        D ⊓ LinearMap.ker L := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hxD, hxL⟩
      exact ⟨⟨x, hxD⟩, hxL, rfl⟩

  have hkerFinrank :
      Module.finrank (ZMod 2) (LinearMap.ker restricted) =
        Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) := by
    rw [← Submodule.finrank_map_subtype_eq D (LinearMap.ker restricted)]
    rw [hkernelMap]
    have hsubmodule :
        D ⊓ LinearMap.ker L = rowSpaceEuclideanRadical G := by
      dsimp [D, L, rowSpaceEuclideanRadical]
      rw [euclideanOrthogonal_rowSpace_eq_ker_mulVecLin]
    rw [hsubmodule]

  have hrowRank :
      Module.finrank (ZMod 2) D = Matrix.rank G := by
    change Module.finrank (ZMod 2) (matrixRowSpace G) = Matrix.rank G
    rw [matrixRowSpace, range_vecMulLinear,
      ← Matrix.rank_eq_finrank_span_row]

  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker restricted
  rw [← hrowRank]
  calc
    Matrix.rank (G * G.transpose) +
          Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G)
        = Module.finrank (ZMod 2) (LinearMap.range restricted) +
            Module.finrank (ZMod 2) (LinearMap.ker restricted) := by
              rw [← hkerFinrank, ← hrange]
              rfl
    _ = Module.finrank (ZMod 2) D := hrankNullity

theorem generatorGramRank_add_euclideanHullFinrank_eq_codeDimension
    {kCl n : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row) :
    Matrix.rank (G * G.transpose) +
        Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) =
      kCl := by
  calc
    Matrix.rank (G * G.transpose) +
          Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G)
        = Matrix.rank G :=
      gramRank_add_rowSpaceRadicalFinrank_eq_rank G
    _ = kCl := by
      simpa using hG.rank_matrix

theorem euclideanHullFinrank_eq_codeDimension_sub_generatorGramRank
    {kCl n : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row) :
    Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) =
      kCl - Matrix.rank (G * G.transpose) := by
  have h :=
    generatorGramRank_add_euclideanHullFinrank_eq_codeDimension G hG
  omega

/- 满行秩生成矩阵与校验矩阵的对应。由正交性与维数互补证明两侧行空间互为欧几里得对偶，
继而证明它们的欧几里得交空间相同，并得到校验矩阵的行内积矩阵秩。
-/
theorem generatorRowSpace_orthogonal_eq_parityCheckRowSpace
    {kCl r n : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row)
    (hH : LinearIndependent (ZMod 2) H.row)
    (hGH : G * H.transpose = 0)
    (hDimension : kCl + r = n) :
    (euclideanBilinForm n).orthogonal (matrixRowSpace G) =
      matrixRowSpace H := by
  have hle :
      matrixRowSpace H ≤
        (euclideanBilinForm n).orthogonal (matrixRowSpace G) := by
    rw [euclideanOrthogonal_rowSpace_eq_ker_mulVecLin]
    change LinearMap.range H.vecMulLinear ≤ LinearMap.ker G.mulVecLin
    rw [← Matrix.mulVecLin_transpose]
    rw [LinearMap.range_le_ker_iff]
    rw [← Matrix.mulVecLin_mul, hGH]
    exact Matrix.mulVecLin_zero

  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hfinrankH :
      Module.finrank (ZMod 2) (matrixRowSpace H) = r := by
    rw [matrixRowSpace, range_vecMulLinear,
      ← Matrix.rank_eq_finrank_span_row]
    simpa using hH.rank_matrix
  have hrankG : Matrix.rank G = kCl := by
    simpa using hG.rank_matrix
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker G.mulVecLin
  have hfinrankKer :
      Module.finrank (ZMod 2) (LinearMap.ker G.mulVecLin) = r := by
    change
      Matrix.rank G +
          Module.finrank (ZMod 2) (LinearMap.ker G.mulVecLin) =
        Module.finrank (ZMod 2) (Fin n → ZMod 2) at hrankNullity
    rw [hrankG, Module.finrank_fin_fun] at hrankNullity
    omega
  have hfinrankOrthogonal :
      Module.finrank (ZMod 2)
          ((euclideanBilinForm n).orthogonal (matrixRowSpace G)) = r := by
    rw [euclideanOrthogonal_rowSpace_eq_ker_mulVecLin]
    exact hfinrankKer
  exact hfinrankH.trans hfinrankOrthogonal.symm

theorem generatorEuclideanHull_eq_parityCheckEuclideanHull
    {kCl r n : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row)
    (hH : LinearIndependent (ZMod 2) H.row)
    (hGH : G * H.transpose = 0)
    (hDimension : kCl + r = n) :
    rowSpaceEuclideanRadical G = rowSpaceEuclideanRadical H := by
  have hGorthogonal :=
    generatorRowSpace_orthogonal_eq_parityCheckRowSpace
      G H hG hH hGH hDimension
  have hHG : H * G.transpose = 0 := by
    have htranspose := congrArg Matrix.transpose hGH
    simpa using htranspose
  have hHorthogonal :=
    generatorRowSpace_orthogonal_eq_parityCheckRowSpace
      H G hH hG hHG (by omega)
  change
    matrixRowSpace G ⊓
        (euclideanBilinForm n).orthogonal (matrixRowSpace G) =
      matrixRowSpace H ⊓
        (euclideanBilinForm n).orthogonal (matrixRowSpace H)
  rw [hGorthogonal, hHorthogonal]
  exact inf_comm _ _

theorem parityCheckGramRank_add_euclideanHullFinrank_eq_rowCount
    {kCl r n : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row)
    (hH : LinearIndependent (ZMod 2) H.row)
    (hGH : G * H.transpose = 0)
    (hDimension : kCl + r = n) :
    Matrix.rank (H * H.transpose) +
        Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) =
      r := by
  rw [generatorEuclideanHull_eq_parityCheckEuclideanHull
    G H hG hH hGH hDimension]
  exact generatorGramRank_add_euclideanHullFinrank_eq_codeDimension H hH

theorem parityCheckGramRank_add_euclideanHullFinrank_eq_codeCodimension
    {kCl r n : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row)
    (hH : LinearIndependent (ZMod 2) H.row)
    (hGH : G * H.transpose = 0)
    (hDimension : kCl + r = n) :
    Matrix.rank (H * H.transpose) +
        Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) =
      n - kCl := by
  have hrowCount :=
    parityCheckGramRank_add_euclideanHullFinrank_eq_rowCount
      G H hG hH hGH hDimension
  omega

theorem parityCheckGramRank_eq_rowCount_sub_euclideanHullFinrank
    {kCl r n : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row)
    (hH : LinearIndependent (ZMod 2) H.row)
    (hGH : G * H.transpose = 0)
    (hDimension : kCl + r = n) :
    Matrix.rank (H * H.transpose) =
      r - Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) := by
  have hrowCount :=
    parityCheckGramRank_add_euclideanHullFinrank_eq_rowCount
      G H hG hH hGH hDimension
  omega

theorem parityCheckGramRank_eq_codeCodimension_sub_euclideanHullFinrank
    {kCl r n : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row)
    (hH : LinearIndependent (ZMod 2) H.row)
    (hGH : G * H.transpose = 0)
    (hDimension : kCl + r = n) :
    Matrix.rank (H * H.transpose) =
      n - kCl -
        Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) := by
  have hcodimension :=
    parityCheckGramRank_add_euclideanHullFinrank_eq_codeCodimension
      G H hG hH hGH hDimension
  omega

open scoped BigOperators

/- 把二元向量分别转换为纯 X、纯 Z 算子。以下给出两种算子的辛坐标及交叉辛内积。
-/
def binaryVectorToPureXPauli {n : ℕ}
    (v : Fin n → ZMod 2) : NQubitPauliGroupElement n :=
  NQubitPauliGroupElement.ofOperator
    (fun q => if v q = 0 then PauliOperator.I else PauliOperator.X)

def binaryVectorToPureZPauli {n : ℕ}
    (v : Fin n → ZMod 2) : NQubitPauliGroupElement n :=
  NQubitPauliGroupElement.ofOperator
    (fun q => if v q = 0 then PauliOperator.I else PauliOperator.Z)

@[simp] theorem binaryVectorToPureXPauli_toSymplectic_X
    {n : ℕ} (v : Fin n → ZMod 2) (q : Fin n) :
    NQubitPauliOperator.toSymplectic
        (binaryVectorToPureXPauli v).operators (Fin.castAdd n q) =
      v q := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  by_cases h : v q = 0
  · simp [binaryVectorToPureXPauli, h]
  · have hv : v q = 1 := by
      generalize hx : v q = x at h ⊢
      fin_cases x
      · exact (h rfl).elim
      · rfl
    simp [binaryVectorToPureXPauli, hv]

@[simp] theorem binaryVectorToPureXPauli_toSymplectic_Z
    {n : ℕ} (v : Fin n → ZMod 2) (q : Fin n) :
    NQubitPauliOperator.toSymplectic
        (binaryVectorToPureXPauli v).operators (Fin.natAdd n q) =
      0 := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  by_cases h : v q = 0 <;> simp [binaryVectorToPureXPauli, h]

@[simp] theorem binaryVectorToPureXPauli_toSymplectic_Z_addNat
    {n : ℕ} (v : Fin n → ZMod 2) (q : Fin n) :
    NQubitPauliOperator.toSymplectic
        (binaryVectorToPureXPauli v).operators (Fin.addNat q n) =
      0 := by
  have hindex : Fin.addNat q n = Fin.natAdd n q := by
    apply Fin.ext
    simp [Fin.addNat, Fin.natAdd]
    omega
  rw [hindex]
  exact binaryVectorToPureXPauli_toSymplectic_Z v q

@[simp] theorem binaryVectorToPureZPauli_toSymplectic_X
    {n : ℕ} (v : Fin n → ZMod 2) (q : Fin n) :
    NQubitPauliOperator.toSymplectic
        (binaryVectorToPureZPauli v).operators (Fin.castAdd n q) =
      0 := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  by_cases h : v q = 0 <;> simp [binaryVectorToPureZPauli, h]

@[simp] theorem binaryVectorToPureZPauli_toSymplectic_Z
    {n : ℕ} (v : Fin n → ZMod 2) (q : Fin n) :
    NQubitPauliOperator.toSymplectic
        (binaryVectorToPureZPauli v).operators (Fin.natAdd n q) =
      v q := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  by_cases h : v q = 0
  · simp [binaryVectorToPureZPauli, h]
  · have hv : v q = 1 := by
      generalize hx : v q = x at h ⊢
      fin_cases x
      · exact (h rfl).elim
      · rfl
    simp [binaryVectorToPureZPauli, hv]

@[simp] theorem binaryVectorToPureZPauli_toSymplectic_Z_addNat
    {n : ℕ} (v : Fin n → ZMod 2) (q : Fin n) :
    NQubitPauliOperator.toSymplectic
        (binaryVectorToPureZPauli v).operators (Fin.addNat q n) =
      v q := by
  have hindex : Fin.addNat q n = Fin.natAdd n q := by
    apply Fin.ext
    simp [Fin.addNat, Fin.natAdd]
    omega
  rw [hindex]
  exact binaryVectorToPureZPauli_toSymplectic_Z v q

/- 将校验矩阵的每一行分别用于纯 X 和纯 Z 生成元，形成 CSS 候选列表。
以下构造其辛检查矩阵与冲突矩阵，并证明线性无关性。
-/
def parityCheckCSSGeneratorFamily {r n : ℕ}
    (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    Fin (r + r) → NQubitPauliGroupElement n :=
  Fin.append
    (fun i : Fin r => binaryVectorToPureXPauli (H.row i))
    (fun i : Fin r => binaryVectorToPureZPauli (H.row i))

@[simp] theorem parityCheckCSSGeneratorFamily_x
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (i : Fin r) :
    parityCheckCSSGeneratorFamily H (Fin.castAdd r i) =
      binaryVectorToPureXPauli (H.row i) :=
  Fin.append_left _ _ _

@[simp] theorem parityCheckCSSGeneratorFamily_z
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (i : Fin r) :
    parityCheckCSSGeneratorFamily H (Fin.natAdd r i) =
      binaryVectorToPureZPauli (H.row i) :=
  Fin.append_right _ _ _

@[simp] theorem parityCheckCSSGeneratorFamily_z_addNat
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (i : Fin r) :
    parityCheckCSSGeneratorFamily H (Fin.addNat i r) =
      binaryVectorToPureZPauli (H.row i) := by
  have hi : Fin.addNat i r = Fin.natAdd r i := by
    apply Fin.ext
    simp [Fin.addNat, Fin.natAdd]
    omega
  calc
    parityCheckCSSGeneratorFamily H (Fin.addNat i r) =
        parityCheckCSSGeneratorFamily H (Fin.natAdd r i) :=
      congrArg (parityCheckCSSGeneratorFamily H) hi
    _ = binaryVectorToPureZPauli (H.row i) :=
      parityCheckCSSGeneratorFamily_z H i

def parityCheckCSSGeneratorList {r n : ℕ}
    (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    List (NQubitPauliGroupElement n) :=
  List.ofFn (parityCheckCSSGeneratorFamily H)

@[simp] theorem parityCheckCSSGeneratorList_length
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    (parityCheckCSSGeneratorList H).length = r + r := by
  simp [parityCheckCSSGeneratorList]

theorem parityCheckCSSGeneratorList_eq_x_append_z
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    parityCheckCSSGeneratorList H =
      List.ofFn (fun i : Fin r => binaryVectorToPureXPauli (H.row i)) ++
      List.ofFn (fun i : Fin r => binaryVectorToPureZPauli (H.row i)) := by
  rw [parityCheckCSSGeneratorList, parityCheckCSSGeneratorFamily,
    List.ofFn_fin_append]

def parityCheckCSSSymplecticMatrix {r n : ℕ}
    (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    Matrix (Fin r ⊕ Fin r) (Fin n ⊕ Fin n) (ZMod 2) :=
  Matrix.fromBlocks H 0 0 H

def parityCheckCSSConflictMatrix {r n : ℕ}
    (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (ZMod 2) :=
  parityCheckCSSSymplecticMatrix H * auxSymplecticMatrix n *
    (parityCheckCSSSymplecticMatrix H).transpose

theorem parityCheckCSSSymplecticMatrix_mul_J_mul_transpose
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    parityCheckCSSSymplecticMatrix H * auxSymplecticMatrix n *
          (parityCheckCSSSymplecticMatrix H).transpose =
      Matrix.fromBlocks 0 (H * H.transpose) (H * H.transpose) 0 := by
  ext (i | i) (j | j) <;>
    simp [parityCheckCSSSymplecticMatrix, auxSymplecticMatrix,
      Matrix.mul_apply]

theorem parityCheckCSSConflictMatrix_eq_blockGram
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    parityCheckCSSConflictMatrix H =
      Matrix.fromBlocks 0 (H * H.transpose) (H * H.transpose) 0 := by
  exact parityCheckCSSSymplecticMatrix_mul_J_mul_transpose H

theorem parityCheckCSSGeneratorFamily_rowsLinearIndependent
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H.row) :
    LinearIndependent (ZMod 2)
      (fun i : Fin (r + r) =>
        NQubitPauliOperator.toSymplectic
          (parityCheckCSSGeneratorFamily H i).operators) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg
  have hXcomb :
      (∑ a : Fin r, f (Fin.castAdd r a) • H.row a) =
        ∑ a : Fin r, g (Fin.castAdd r a) • H.row a := by
    funext q
    have hq := congrFun hfg (Fin.castAdd n q)
    simpa [Fin.sum_univ_add, Pi.smul_apply, Fin.append_left,
      Fin.append_right] using hq
  have hZcomb :
      (∑ a : Fin r, f (Fin.natAdd r a) • H.row a) =
        ∑ a : Fin r, g (Fin.natAdd r a) • H.row a := by
    funext q
    have hq := congrFun hfg (Fin.natAdd n q)
    simpa [Fin.sum_univ_add, Pi.smul_apply, Fin.append_left,
      Fin.append_right] using hq
  have hXcoeff :
      ∀ a : Fin r, f (Fin.castAdd r a) = g (Fin.castAdd r a) :=
    (Fintype.linearIndependent_iffₛ.mp hH) _ _ hXcomb
  have hZcoeff :
      ∀ a : Fin r, f (Fin.natAdd r a) = g (Fin.natAdd r a) :=
    (Fintype.linearIndependent_iffₛ.mp hH) _ _ hZcomb
  exact Fin.addCases hXcoeff hZcoeff

theorem parityCheckCSSGeneratorList_rowsLinearIndependent
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H.row) :
    NQubitPauliGroupElement.rowsLinearIndependent
      (parityCheckCSSGeneratorList H) := by
  let e :
      Fin (parityCheckCSSGeneratorList H).length ≃ Fin (r + r) :=
    finCongr (parityCheckCSSGeneratorList_length H)
  have hfamily :=
    parityCheckCSSGeneratorFamily_rowsLinearIndependent H hH
  have hreindexed :
      LinearIndependent (ZMod 2)
        ((fun i : Fin (r + r) =>
            NQubitPauliOperator.toSymplectic
              (parityCheckCSSGeneratorFamily H i).operators) ∘ e) :=
    (linearIndependent_equiv e).mpr hfamily
  rw [NQubitPauliGroupElement.rowsLinearIndependent]
  have hpointwise :
      (fun i : Fin (parityCheckCSSGeneratorList H).length =>
          NQubitPauliGroupElement.checkMatrix
            (parityCheckCSSGeneratorList H) i) =
        ((fun i : Fin (r + r) =>
            NQubitPauliOperator.toSymplectic
              (parityCheckCSSGeneratorFamily H i).operators) ∘ e) := by
    funext i j
    unfold NQubitPauliGroupElement.checkMatrix
    simp only [parityCheckCSSGeneratorList, List.get_ofFn,
      Function.comp_apply]
    apply congrArg (fun a : Fin (r + r) =>
      NQubitPauliOperator.toSymplectic
        (parityCheckCSSGeneratorFamily H a).operators j)
    apply Fin.ext
    change (i : ℕ) = (finCongr _ i : ℕ)
    rfl
  rw [hpointwise]
  exact hreindexed

def parityCheckCSSCandidate
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H.row) :
    GeneratorListCandidate n where
  generatorsList := parityCheckCSSGeneratorList H
  generators_phaseZero := by
    apply NQubitPauliGroupElement.AllPhaseZero_ofFn
    intro i
    change (parityCheckCSSGeneratorFamily H i).phasePower = 0
    exact Fin.addCases
      (fun a => by simp [binaryVectorToPureXPauli])
      (fun a => by simp [binaryVectorToPureZPauli])
      i
  generators_rowsIndependent :=
    parityCheckCSSGeneratorList_rowsLinearIndependent H hH

theorem pureXPauli_symplecticInner_pureXPauli
    {n : ℕ} (v w : Fin n → ZMod 2) :
    NQubitPauliOperator.symplecticInner
      (binaryVectorToPureXPauli v).operators
      (binaryVectorToPureXPauli w).operators = 0 := by
  unfold NQubitPauliOperator.symplecticInner
  apply Finset.sum_eq_zero
  intro q _
  unfold PauliOperator.symplecticProductSingle
  rw [← NQubitPauliOperator.toSymplectic_X_part
      (binaryVectorToPureXPauli v).operators q,
    ← NQubitPauliOperator.toSymplectic_Z_part
      (binaryVectorToPureXPauli w).operators q,
    ← NQubitPauliOperator.toSymplectic_Z_part
      (binaryVectorToPureXPauli v).operators q,
    ← NQubitPauliOperator.toSymplectic_X_part
      (binaryVectorToPureXPauli w).operators q]
  simp

theorem pureZPauli_symplecticInner_pureZPauli
    {n : ℕ} (v w : Fin n → ZMod 2) :
    NQubitPauliOperator.symplecticInner
      (binaryVectorToPureZPauli v).operators
      (binaryVectorToPureZPauli w).operators = 0 := by
  unfold NQubitPauliOperator.symplecticInner
  apply Finset.sum_eq_zero
  intro q _
  unfold PauliOperator.symplecticProductSingle
  rw [← NQubitPauliOperator.toSymplectic_X_part
      (binaryVectorToPureZPauli v).operators q,
    ← NQubitPauliOperator.toSymplectic_Z_part
      (binaryVectorToPureZPauli w).operators q,
    ← NQubitPauliOperator.toSymplectic_Z_part
      (binaryVectorToPureZPauli v).operators q,
    ← NQubitPauliOperator.toSymplectic_X_part
      (binaryVectorToPureZPauli w).operators q]
  simp

theorem pureXPauli_symplecticInner_pureZPauli_eq_dotProduct
    {n : ℕ} (v w : Fin n → ZMod 2) :
    NQubitPauliOperator.symplecticInner
      (binaryVectorToPureXPauli v).operators
      (binaryVectorToPureZPauli w).operators =
        ∑ q, v q * w q := by
  unfold NQubitPauliOperator.symplecticInner
  apply Finset.sum_congr rfl
  intro q _
  unfold PauliOperator.symplecticProductSingle
  rw [← NQubitPauliOperator.toSymplectic_X_part
      (binaryVectorToPureXPauli v).operators q,
    ← NQubitPauliOperator.toSymplectic_Z_part
      (binaryVectorToPureZPauli w).operators q,
    ← NQubitPauliOperator.toSymplectic_Z_part
      (binaryVectorToPureXPauli v).operators q,
    ← NQubitPauliOperator.toSymplectic_X_part
      (binaryVectorToPureZPauli w).operators q]
  simp

theorem pureZPauli_symplecticInner_pureXPauli_eq_dotProduct
    {n : ℕ} (v w : Fin n → ZMod 2) :
    NQubitPauliOperator.symplecticInner
      (binaryVectorToPureZPauli v).operators
      (binaryVectorToPureXPauli w).operators =
        ∑ q, v q * w q := by
  unfold NQubitPauliOperator.symplecticInner
  apply Finset.sum_congr rfl
  intro q _
  unfold PauliOperator.symplecticProductSingle
  rw [← NQubitPauliOperator.toSymplectic_X_part
      (binaryVectorToPureZPauli v).operators q,
    ← NQubitPauliOperator.toSymplectic_Z_part
      (binaryVectorToPureXPauli w).operators q,
    ← NQubitPauliOperator.toSymplectic_Z_part
      (binaryVectorToPureZPauli v).operators q,
    ← NQubitPauliOperator.toSymplectic_X_part
      (binaryVectorToPureXPauli w).operators q]
  simp

def parityCheckCSSIndexEquiv {r n : ℕ}
    (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    Fin (parityCheckCSSGeneratorList H).length ≃ (Fin r ⊕ Fin r) :=
  (finCongr (parityCheckCSSGeneratorList_length H)).trans
    finSumFinEquiv.symm

@[simp] theorem parityCheckCSSGeneratorList_get_inl
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (i : Fin r) :
    (parityCheckCSSGeneratorList H).get
        ((parityCheckCSSIndexEquiv H).symm (Sum.inl i)) =
      binaryVectorToPureXPauli (H.row i) := by
  unfold parityCheckCSSIndexEquiv parityCheckCSSGeneratorList
  simp only [Equiv.symm_trans_apply, List.get_ofFn]
  calc
    parityCheckCSSGeneratorFamily H
        (Fin.cast _ ((finCongr _).symm
          (finSumFinEquiv.symm.symm (Sum.inl i)))) =
        parityCheckCSSGeneratorFamily H (Fin.castAdd r i) := by
      apply congrArg (parityCheckCSSGeneratorFamily H)
      apply Fin.ext
      rfl
    _ = binaryVectorToPureXPauli (H.row i) :=
      parityCheckCSSGeneratorFamily_x H i

@[simp] theorem parityCheckCSSGeneratorList_get_inr
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) (i : Fin r) :
    (parityCheckCSSGeneratorList H).get
        ((parityCheckCSSIndexEquiv H).symm (Sum.inr i)) =
      binaryVectorToPureZPauli (H.row i) := by
  unfold parityCheckCSSIndexEquiv parityCheckCSSGeneratorList
  simp only [Equiv.symm_trans_apply, List.get_ofFn]
  calc
    parityCheckCSSGeneratorFamily H
        (Fin.cast _ ((finCongr _).symm
          (finSumFinEquiv.symm.symm (Sum.inr i)))) =
        parityCheckCSSGeneratorFamily H (Fin.natAdd r i) := by
      apply congrArg (parityCheckCSSGeneratorFamily H)
      apply Fin.ext
      simp
    _ = binaryVectorToPureZPauli (H.row i) :=
      parityCheckCSSGeneratorFamily_z H i

theorem parityCheckCSSGeneratorList_checkMatrix_eq_symplecticMatrix
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    Matrix.reindex
        (parityCheckCSSIndexEquiv H)
        finSumFinEquiv.symm
        (NQubitPauliGroupElement.checkMatrix
          (parityCheckCSSGeneratorList H)) =
      parityCheckCSSSymplecticMatrix H := by
  ext (i | i) (j | j)
  all_goals rw [Matrix.reindex_apply]
  all_goals unfold Matrix.submatrix
  all_goals simp only [Matrix.of_apply]
  all_goals unfold NQubitPauliGroupElement.checkMatrix
  · rw [parityCheckCSSGeneratorList_get_inl]
    exact binaryVectorToPureXPauli_toSymplectic_X _ _
  · rw [parityCheckCSSGeneratorList_get_inl]
    simp [parityCheckCSSSymplecticMatrix]
  · rw [parityCheckCSSGeneratorList_get_inr]
    exact binaryVectorToPureZPauli_toSymplectic_X _ _
  · rw [parityCheckCSSGeneratorList_get_inr]
    simp [parityCheckCSSSymplecticMatrix]

@[simp] theorem parityCheckCSSCandidate_get_inl
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H.row) (i : Fin r) :
    ((parityCheckCSSCandidate H hH).generatorsList.get
      ((parityCheckCSSIndexEquiv H).symm (Sum.inl i))) =
        binaryVectorToPureXPauli (H.row i) := by
  unfold parityCheckCSSCandidate parityCheckCSSIndexEquiv
  unfold parityCheckCSSGeneratorList
  simp only [Equiv.symm_trans_apply, List.get_ofFn]
  calc
    parityCheckCSSGeneratorFamily H
        (Fin.cast _ ((finCongr _).symm
          (finSumFinEquiv.symm.symm (Sum.inl i)))) =
        parityCheckCSSGeneratorFamily H (Fin.castAdd r i) := by
      apply congrArg (parityCheckCSSGeneratorFamily H)
      apply Fin.ext
      rfl
    _ = binaryVectorToPureXPauli (H.row i) :=
      parityCheckCSSGeneratorFamily_x H i

@[simp] theorem parityCheckCSSCandidate_get_inr
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H.row) (i : Fin r) :
    ((parityCheckCSSCandidate H hH).generatorsList.get
      ((parityCheckCSSIndexEquiv H).symm (Sum.inr i))) =
        binaryVectorToPureZPauli (H.row i) := by
  unfold parityCheckCSSCandidate parityCheckCSSIndexEquiv
  unfold parityCheckCSSGeneratorList
  simp only [Equiv.symm_trans_apply, List.get_ofFn]
  calc
    parityCheckCSSGeneratorFamily H
        (Fin.cast _ ((finCongr _).symm
          (finSumFinEquiv.symm.symm (Sum.inr i)))) =
        parityCheckCSSGeneratorFamily H (Fin.natAdd r i) := by
      apply congrArg (parityCheckCSSGeneratorFamily H)
      apply Fin.ext
      simp
    _ = binaryVectorToPureZPauli (H.row i) :=
      parityCheckCSSGeneratorFamily_z H i

/- 直积子空间的维数及分块矩阵的秩。用于证明 CSS 冲突矩阵秩是校验矩阵行内积矩阵秩的两倍。
-/
private def submoduleProdLinearEquiv
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (S : Submodule R M) (T : Submodule R N) :
    S.prod T ≃ₗ[R] S × T where
  toFun x :=
    (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x :=
    ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
  left_inv x := by
    ext <;> rfl
  right_inv x := by
    ext <;> rfl
  map_add' x y := by
    rfl
  map_smul' a x := by
    rfl

private theorem finrank_submodule_prod
    {R M N : Type*} [Field R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (S : Submodule R M) (T : Submodule R N) :
    Module.finrank R (S.prod T) =
      Module.finrank R S + Module.finrank R T := by
  rw [LinearEquiv.finrank_eq (submoduleProdLinearEquiv S T)]
  exact Module.finrank_prod

private theorem rank_fromBlocks_diagonal_same
    {R ι : Type*} [Field R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    Matrix.rank (Matrix.fromBlocks A 0 0 A) =
      Matrix.rank A + Matrix.rank A := by
  let b := Pi.basisFun R ι
  let f : Module.End R (ι → R) := Matrix.toLin b b A
  have hmatrix :
      Matrix.fromBlocks A 0 0 A =
        LinearMap.toMatrix (b.prod b) (b.prod b) (f.prodMap f) := by
    rw [LinearMap.toMatrix_prodMap]
    simp only [f, LinearMap.toMatrix_toLin]
  rw [hmatrix]
  rw [Matrix.rank_eq_finrank_range_toLin _ (b.prod b) (b.prod b)]
  rw [Matrix.toLin_toMatrix, LinearMap.range_prodMap]
  rw [finrank_submodule_prod]
  change
    Module.finrank R (LinearMap.range f) +
        Module.finrank R (LinearMap.range f) =
      Matrix.rank A + Matrix.rank A
  rw [Matrix.rank_eq_finrank_range_toLin A b b]

private theorem rank_fromBlocks_antidiagonal_same
    {R ι : Type*} [Field R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) :
    Matrix.rank (Matrix.fromBlocks 0 A A 0) =
      2 * Matrix.rank A := by
  let anti : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
    Matrix.fromBlocks 0 A A 0
  let diagonal : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
    Matrix.fromBlocks A 0 0 A
  have hswap :
      anti.submatrix (Equiv.sumComm ι ι) (Equiv.refl (ι ⊕ ι)) =
        diagonal := by
    ext (i | i) (j | j) <;>
      simp [anti, diagonal, Matrix.submatrix]
  calc
    Matrix.rank (Matrix.fromBlocks 0 A A 0) =
        Matrix.rank anti := rfl
    _ = Matrix.rank
        (anti.submatrix (Equiv.sumComm ι ι) (Equiv.refl (ι ⊕ ι))) :=
      (Matrix.rank_submatrix anti (Equiv.sumComm ι ι)
        (Equiv.refl (ι ⊕ ι))).symm
    _ = Matrix.rank diagonal := by rw [hswap]
    _ = Matrix.rank A + Matrix.rank A :=
      rank_fromBlocks_diagonal_same A
    _ = 2 * Matrix.rank A := by omega

theorem parityCheckCSSConflictMatrix_rank
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2)) :
    Matrix.rank (parityCheckCSSConflictMatrix H) =
      2 * Matrix.rank (H * H.transpose) := by
  rw [parityCheckCSSConflictMatrix_eq_blockGram]
  exact rank_fromBlocks_antidiagonal_same (H * H.transpose)

namespace ParityCheckCSSCandidate

/- CSS 候选生成元的冲突矩阵与纠缠数。以下把纠缠参数写成余维减去欧几里得交空间维数，
并证明任何恢复同一候选生成元的辅助扩展都满足该下界。
-/
theorem conflictMatrix_eq_blockGram
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H.row) :
    Matrix.reindex (parityCheckCSSIndexEquiv H)
        (parityCheckCSSIndexEquiv H)
        (GeneratorListCandidate.conflictMatrix
          (parityCheckCSSCandidate H hH)) =
      Matrix.fromBlocks 0 (H * H.transpose) (H * H.transpose) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals rw [Matrix.reindex_apply]
  all_goals unfold Matrix.submatrix
  all_goals simp only [Matrix.of_apply]
  all_goals rw [GeneratorListCandidate.conflictMatrix_apply]
  · rw [parityCheckCSSCandidate_get_inl, parityCheckCSSCandidate_get_inl]
    exact pureXPauli_symplecticInner_pureXPauli _ _
  · rw [parityCheckCSSCandidate_get_inl, parityCheckCSSCandidate_get_inr,
      pureXPauli_symplecticInner_pureZPauli_eq_dotProduct]
    simp [Matrix.mul_apply]
  · rw [parityCheckCSSCandidate_get_inr, parityCheckCSSCandidate_get_inl,
      pureZPauli_symplecticInner_pureXPauli_eq_dotProduct]
    simp [Matrix.mul_apply]
  · rw [parityCheckCSSCandidate_get_inr, parityCheckCSSCandidate_get_inr]
    exact pureZPauli_symplecticInner_pureZPauli _ _

theorem conflictRank_eq_two_mul_gramRank
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H.row) :
    GeneratorListCandidate.conflictRank
        (parityCheckCSSCandidate H hH) =
      2 * Matrix.rank (H * H.transpose) := by
  unfold GeneratorListCandidate.conflictRank
  calc
    Matrix.rank (GeneratorListCandidate.conflictMatrix
        (parityCheckCSSCandidate H hH)) =
        Matrix.rank (Matrix.reindex (parityCheckCSSIndexEquiv H)
          (parityCheckCSSIndexEquiv H)
          (GeneratorListCandidate.conflictMatrix
            (parityCheckCSSCandidate H hH))) :=
      (Matrix.rank_reindex (parityCheckCSSIndexEquiv H)
        (parityCheckCSSIndexEquiv H)
        (GeneratorListCandidate.conflictMatrix
          (parityCheckCSSCandidate H hH))).symm
    _ = Matrix.rank
        (Matrix.fromBlocks 0 (H * H.transpose) (H * H.transpose) 0) := by
      rw [conflictMatrix_eq_blockGram]
    _ = 2 * Matrix.rank (H * H.transpose) :=
      rank_fromBlocks_antidiagonal_same (H * H.transpose)

theorem conflictRank_even
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H.row) :
    Even (GeneratorListCandidate.conflictRank
      (parityCheckCSSCandidate H hH)) := by
  refine ⟨Matrix.rank (H * H.transpose), ?_⟩
  rw [conflictRank_eq_two_mul_gramRank]
  omega

theorem ebitCount_eq_gramRank
    {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H.row) :
    GeneratorListCandidate.ebitCount
        (parityCheckCSSCandidate H hH) =
      Matrix.rank (H * H.transpose) := by
  have htwo :=
    GeneratorListCandidate.two_mul_ebitCount_eq_conflictRank_of_even
      (parityCheckCSSCandidate H hH) (conflictRank_even H hH)
  rw [conflictRank_eq_two_mul_gramRank] at htwo
  omega

theorem ebitCount_add_euclideanHullFinrank_eq_rowCount
    {kCl r n : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row)
    (hH : LinearIndependent (ZMod 2) H.row)
    (hGH : G * H.transpose = 0)
    (hDimension : kCl + r = n) :
    GeneratorListCandidate.ebitCount (parityCheckCSSCandidate H hH) +
        Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) =
      r := by
  rw [ebitCount_eq_gramRank]
  exact parityCheckGramRank_add_euclideanHullFinrank_eq_rowCount
    G H hG hH hGH hDimension

theorem ebitCount_add_euclideanHullFinrank_eq_codeCodimension
    {kCl r n : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row)
    (hH : LinearIndependent (ZMod 2) H.row)
    (hGH : G * H.transpose = 0)
    (hDimension : kCl + r = n) :
    GeneratorListCandidate.ebitCount (parityCheckCSSCandidate H hH) +
        Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) =
      n - kCl := by
  have hrowCount :=
    ebitCount_add_euclideanHullFinrank_eq_rowCount
      G H hG hH hGH hDimension
  omega

theorem ebitCount_eq_codeCodimension_sub_euclideanHullFinrank
    {kCl r n : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row)
    (hH : LinearIndependent (ZMod 2) H.row)
    (hGH : G * H.transpose = 0)
    (hDimension : kCl + r = n) :
    GeneratorListCandidate.ebitCount (parityCheckCSSCandidate H hH) =
      n - kCl -
        Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) := by
  have hcodimension :=
    ebitCount_add_euclideanHullFinrank_eq_codeCodimension
      G H hG hH hGH hDimension
  omega

theorem gramRank_le_of_canExtendWith
    {r n c' : ℕ}
    (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H.row)
    (hExtend :
      CanExtendWith (parityCheckCSSCandidate H hH) c') :
    Matrix.rank (H * H.transpose) ≤ c' := by
  rw [← ebitCount_eq_gramRank H hH]
  exact GeneratorListCandidate.ebitCount_le_of_canExtendWith
    (parityCheckCSSCandidate H hH) hExtend

theorem codeCodimension_sub_euclideanHullFinrank_le_of_canExtendWith
    {kCl r n c' : ℕ}
    (G : Matrix (Fin kCl) (Fin n) (ZMod 2))
    (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hG : LinearIndependent (ZMod 2) G.row)
    (hH : LinearIndependent (ZMod 2) H.row)
    (hGH : G * H.transpose = 0)
    (hDimension : kCl + r = n)
    (hExtend :
      CanExtendWith (parityCheckCSSCandidate H hH) c') :
    n - kCl -
        Module.finrank (ZMod 2) (rowSpaceEuclideanRadical G) ≤
      c' := by
  rw [← ebitCount_eq_codeCodimension_sub_euclideanHullFinrank
    G H hG hH hGH hDimension]
  exact GeneratorListCandidate.ebitCount_le_of_canExtendWith
    (parityCheckCSSCandidate H hH) hExtend

end ParityCheckCSSCandidate

namespace BinaryCode12_7_3EuclideanHull2

/-- Kim 实例的二元生成矩阵。按文献行列顺序录入 7 行、12 列矩阵。
后续在 Lean 中证明其行线性无关、行空间维数为 7、行内积矩阵秩为 5，
从而得到欧几里得交空间维数为 2。文献给出的经典码距离不作为这里的已证明结论。
-/
def kimGeneratorMatrix : Matrix (Fin 7) (Fin 12) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1;
     1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1;
     1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0;
     1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0]

private theorem rowsLinearIndependent_of_mul_eq_one
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (B : Matrix (Fin n) (Fin m) (ZMod 2))
    (hAB : A * B = 1) :
    LinearIndependent (ZMod 2) A.row := by
  rw [← Matrix.vecMul_injective_iff]
  intro x y hxy
  have hright := congrArg (fun v => Matrix.vecMul v B) hxy
  simpa [Matrix.vecMul_vecMul, hAB] using hright

/- 生成矩阵的显式右逆，用于证明行线性无关与秩为 7。
-/
private def generatorRightInverse :
    Matrix (Fin 12) (Fin 7) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 1, 0;
     1, 0, 0, 0, 0, 1, 1;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 1, 0;
     0, 0, 0, 1, 0, 1, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0]

theorem generatorRowsLinearIndependent :
    LinearIndependent (ZMod 2) kimGeneratorMatrix.row := by
  apply rowsLinearIndependent_of_mul_eq_one
    kimGeneratorMatrix generatorRightInverse
  native_decide

theorem generatorRank : Matrix.rank kimGeneratorMatrix = 7 := by
  simpa using generatorRowsLinearIndependent.rank_matrix

/- 生成矩阵行内积矩阵的独立行及分解，用于证明其秩为 5 和欧几里得交空间维数为 2。
-/
private def generatorGramRowBasis :
    Matrix (Fin 5) (Fin 7) (ZMod 2) :=
  !![0, 1, 1, 1, 1, 0, 1;
     0, 1, 0, 0, 0, 0, 1;
     0, 1, 0, 1, 0, 1, 0;
     0, 1, 0, 0, 1, 1, 1;
     0, 1, 1, 0, 1, 1, 1]

private def generatorGramLeftFactor :
    Matrix (Fin 7) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 0;
     1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 1, 1, 0;
     0, 0, 0, 0, 1]

private def generatorGramRowBasisRightInverse :
    Matrix (Fin 7) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 0;
     1, 0, 1, 0, 1;
     0, 0, 0, 1, 1;
     1, 0, 0, 0, 1;
     0, 1, 0, 1, 0;
     0, 0, 0, 0, 0;
     1, 1, 1, 0, 1]

private def generatorGramIndependentRowIndex : Fin 5 → Fin 7 :=
  ![1, 2, 3, 4, 6]

theorem generatorGramRank :
    Matrix.rank (kimGeneratorMatrix * kimGeneratorMatrix.transpose) = 5 := by
  have hfactor :
      kimGeneratorMatrix * kimGeneratorMatrix.transpose =
        generatorGramLeftFactor * generatorGramRowBasis := by
    native_decide
  have hrightInverse :
      generatorGramRowBasis * generatorGramRowBasisRightInverse = 1 := by
    native_decide
  have hrowIndependent :
      LinearIndependent (ZMod 2) generatorGramRowBasis.row :=
    rowsLinearIndependent_of_mul_eq_one
      generatorGramRowBasis generatorGramRowBasisRightInverse hrightInverse
  have hrankBasis : Matrix.rank generatorGramRowBasis = 5 := by
    simpa using hrowIndependent.rank_matrix
  have hupper :
      Matrix.rank (kimGeneratorMatrix * kimGeneratorMatrix.transpose) ≤
        Matrix.rank generatorGramRowBasis := by
    rw [hfactor]
    exact Matrix.rank_mul_le_right _ _
  have hsubmatrix :
      (kimGeneratorMatrix * kimGeneratorMatrix.transpose).submatrix
          generatorGramIndependentRowIndex (Equiv.refl (Fin 7)) =
        generatorGramRowBasis := by
    native_decide
  have hlower :
      Matrix.rank generatorGramRowBasis ≤
        Matrix.rank (kimGeneratorMatrix * kimGeneratorMatrix.transpose) := by
    rw [← hsubmatrix]
    exact Matrix.rank_submatrix_le
      (kimGeneratorMatrix * kimGeneratorMatrix.transpose)
      generatorGramIndependentRowIndex (Equiv.refl (Fin 7))
  omega

theorem euclideanHullFinrank :
    Module.finrank (ZMod 2)
        (rowSpaceEuclideanRadical kimGeneratorMatrix) = 2 := by
  rw [euclideanHullFinrank_eq_codeDimension_sub_generatorGramRank
    kimGeneratorMatrix generatorRowsLinearIndependent]
  rw [generatorGramRank]

/-- 该二元码的显式 5 行、12 列校验矩阵。
以下证明它满行秩、与生成矩阵正交，且行空间恰为生成码的欧几里得对偶。
-/
def parityCheckMatrix : Matrix (Fin 5) (Fin 12) (ZMod 2) :=
  !![1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0;
     1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0;
     0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0;
     1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0;
     0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]

private def parityCheckRightInverse :
    Matrix (Fin 12) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     1, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1]

theorem generator_mul_parityCheckTranspose :
    kimGeneratorMatrix * parityCheckMatrix.transpose = 0 := by
  native_decide

theorem parityCheckRowsLinearIndependent :
    LinearIndependent (ZMod 2) parityCheckMatrix.row := by
  apply rowsLinearIndependent_of_mul_eq_one
    parityCheckMatrix parityCheckRightInverse
  native_decide

theorem parityCheckRank : Matrix.rank parityCheckMatrix = 5 := by
  simpa using parityCheckRowsLinearIndependent.rank_matrix

theorem parityCheckRowSpace_eq_generatorRowSpace_orthogonal :
    matrixRowSpace parityCheckMatrix =
      (euclideanBilinForm 12).orthogonal
        (matrixRowSpace kimGeneratorMatrix) := by
  symm
  exact generatorRowSpace_orthogonal_eq_parityCheckRowSpace
    kimGeneratorMatrix parityCheckMatrix
    generatorRowsLinearIndependent parityCheckRowsLinearIndependent
    generator_mul_parityCheckTranspose (by norm_num)

theorem generatorHull_eq_parityCheckHull :
    rowSpaceEuclideanRadical kimGeneratorMatrix =
      rowSpaceEuclideanRadical parityCheckMatrix := by
  exact generatorEuclideanHull_eq_parityCheckEuclideanHull
    kimGeneratorMatrix parityCheckMatrix
    generatorRowsLinearIndependent parityCheckRowsLinearIndependent
    generator_mul_parityCheckTranspose (by norm_num)

theorem parityCheckGramRank :
    Matrix.rank (parityCheckMatrix * parityCheckMatrix.transpose) = 3 := by
  have h :=
    parityCheckGramRank_eq_codeCodimension_sub_euclideanHullFinrank
      kimGeneratorMatrix parityCheckMatrix
      generatorRowsLinearIndependent parityCheckRowsLinearIndependent
      generator_mul_parityCheckTranspose (by norm_num)
  rw [euclideanHullFinrank] at h
  norm_num at h ⊢
  exact h

/- 由上述校验矩阵构造 Kim 实例的 CSS 辛矩阵与候选 Pauli 生成元。
以下证明冲突秩为 6、纠缠参数为 3，以及固定候选生成元下的辅助量子比特数下界。
-/
def cssSymplecticMatrix :
    Matrix (Fin 5 ⊕ Fin 5) (Fin 12 ⊕ Fin 12) (ZMod 2) :=
  parityCheckCSSSymplecticMatrix parityCheckMatrix

def cssConflictMatrix :
    Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) (ZMod 2) :=
  parityCheckCSSConflictMatrix parityCheckMatrix

theorem cssSymplecticMatrix_mul_J_mul_transpose :
    cssSymplecticMatrix * auxSymplecticMatrix 12 *
          cssSymplecticMatrix.transpose =
      Matrix.fromBlocks
        0
        (parityCheckMatrix * parityCheckMatrix.transpose)
        (parityCheckMatrix * parityCheckMatrix.transpose)
        0 := by
  exact parityCheckCSSSymplecticMatrix_mul_J_mul_transpose parityCheckMatrix

theorem cssConflictMatrix_eq_blockGram :
    cssConflictMatrix =
      Matrix.fromBlocks
        0
        (parityCheckMatrix * parityCheckMatrix.transpose)
        (parityCheckMatrix * parityCheckMatrix.transpose)
        0 := by
  exact parityCheckCSSConflictMatrix_eq_blockGram parityCheckMatrix

theorem cssConflictMatrix_rank :
    Matrix.rank cssConflictMatrix =
      2 * Matrix.rank
        (parityCheckMatrix * parityCheckMatrix.transpose) := by
  exact parityCheckCSSConflictMatrix_rank parityCheckMatrix

def cssPauliCandidate : GeneratorListCandidate 12 :=
  parityCheckCSSCandidate
    parityCheckMatrix parityCheckRowsLinearIndependent

theorem cssPauliCandidate_checkMatrix_eq_symplecticMatrix :
    Matrix.reindex
        (parityCheckCSSIndexEquiv parityCheckMatrix)
        finSumFinEquiv.symm
        (NQubitPauliGroupElement.checkMatrix
          cssPauliCandidate.generatorsList) =
      cssSymplecticMatrix := by
  simpa [cssPauliCandidate, cssSymplecticMatrix] using
    (parityCheckCSSGeneratorList_checkMatrix_eq_symplecticMatrix
      parityCheckMatrix)

@[simp] theorem cssPauliCandidate_generators_length :
    cssPauliCandidate.generatorsList.length = 10 := by
  simp [cssPauliCandidate, parityCheckCSSCandidate]

theorem cssPauliCandidate_generators_phaseZero :
    NQubitPauliGroupElement.AllPhaseZero
      cssPauliCandidate.generatorsList :=
  cssPauliCandidate.generators_phaseZero

theorem cssPauliCandidate_generators_rowsIndependent :
    NQubitPauliGroupElement.rowsLinearIndependent
      cssPauliCandidate.generatorsList :=
  cssPauliCandidate.generators_rowsIndependent

theorem cssPauliCandidate_conflictMatrix_eq_blockGram :
    Matrix.reindex
        (parityCheckCSSIndexEquiv parityCheckMatrix)
        (parityCheckCSSIndexEquiv parityCheckMatrix)
        (GeneratorListCandidate.conflictMatrix cssPauliCandidate) =
      Matrix.fromBlocks
        0
        (parityCheckMatrix * parityCheckMatrix.transpose)
        (parityCheckMatrix * parityCheckMatrix.transpose)
        0 := by
  simpa [cssPauliCandidate] using
    (ParityCheckCSSCandidate.conflictMatrix_eq_blockGram
      parityCheckMatrix parityCheckRowsLinearIndependent)

theorem pauliConflictRank :
    GeneratorListCandidate.conflictRank cssPauliCandidate = 6 := by
  change GeneratorListCandidate.conflictRank
    (parityCheckCSSCandidate
      parityCheckMatrix parityCheckRowsLinearIndependent) = 6
  rw [ParityCheckCSSCandidate.conflictRank_eq_two_mul_gramRank]
  rw [parityCheckGramRank]

theorem pauliEbitCount :
    GeneratorListCandidate.ebitCount cssPauliCandidate = 3 := by
  change GeneratorListCandidate.ebitCount
    (parityCheckCSSCandidate
      parityCheckMatrix parityCheckRowsLinearIndependent) = 3
  rw [ParityCheckCSSCandidate.ebitCount_eq_gramRank]
  exact parityCheckGramRank

theorem auxiliaryCount_lowerBound
    {c' : ℕ}
    (hExtend : CanExtendWith cssPauliCandidate c') :
    3 ≤ c' := by
  rw [← pauliEbitCount]
  exact GeneratorListCandidate.ebitCount_le_of_canExtendWith
    cssPauliCandidate hExtend

end BinaryCode12_7_3EuclideanHull2

end BinaryEuclideanHull

end Quantum
