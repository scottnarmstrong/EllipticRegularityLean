# Results and their Lean statements

Numbers refer to the manuscript. The table lists every theorem, proposition, lemma,
corollary, definition and example of the manuscript that is formalized, by chapter and
section. Rows with a statement file are the main results: the statement file
gives the theorem exactly as it is stated in Lean, and every declaration named
in the row is proved in the libraries. Rows marked "—" in the last column are
proved as ordinary theorems (or are definitions) inside `PDEFoundation` or
`EllipticRegularity`; the declaration name locates them (for example with
`grep -rn "theorem exists_affine_normalization"`), and where several files are
listed they together carry the proof. All declarations live in the namespace
`PDE`.

Remarks and exercises of the manuscript are not formalized, and one item is not
part of the formalized results:

- Remark 4.29 records statements (a) and (b) for context only; they are
  stated in the manuscript without proof.

Notes on individual statements:

- **Isoperimetric inequality (Proposition 1.1).** The inequality is formalized;
  the manuscript does not prove the equality case, and neither does the Lean
  statement. The Lean statement assumes that `E` is nonempty (for `d = 1` the inequality
  fails for the empty set).
- **Prékopa–Leindler inequality (Theorem 1.2).** The manuscript states the
  inequality for nonnegative measurable functions; the Lean statement takes `f`, `g`, `h`
  nonnegative and integrable. The general case follows by truncation.
- **Weak-type (1,1) endpoint for the Newtonian potential.** The statement
  `PDE.exists_newtonPotential_weakTypeOne` (the `NewtonWeakType` challenge) is not a
  numbered result of the manuscript. It is the weak-type (1,1) endpoint for the Newtonian potential
  that supports the Calderón–Zygmund estimates of Section 3.2, and is listed with
  its companion statements below.
- **Meyers' example (Proposition 4.26) and the sharp Hölder exponent in `d = 2`
  (Proposition 4.27).** `PDE.meyers_example` and `PDE.sharp2d_not_holder` take
  the coefficient field `a x = I + (Λ-1) x⊗x/|x|²` for `x ≠ 0` and
  `a 0 = (1 : Mat d)`, the identity matrix; the ascription `(1 : Mat d)` is
  essential, since a bare `1` in that position elaborates as the matrix with
  all entries equal to one, which is not elliptic.
- **Alt–Caffarelli–Friedman (Theorem 2.13)** is stated for `d ≥ 3`; finiteness
  of the functional is part of the conclusion.


### Chapter 1. Function spaces and functional inequalities


**1.1 The isoperimetric inequality**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Proposition 1.1 | Isoperimetric inequality | `PDE.isoperimetric_inequality` | [`Ch1Statements/Isoperimetric.lean`](Ch1Statements/Isoperimetric.lean) |
| Theorem 1.2 | Prékopa–Leindler inequality | `PDE.prekopa_leindler` | [`Ch1Statements/PrekopaLeindler.lean`](Ch1Statements/PrekopaLeindler.lean) |
| Theorem 1.3 | Brunn–Minkowski inequality | `PDE.brunn_minkowski` | [`Ch1Statements/BrunnMinkowski.lean`](Ch1Statements/BrunnMinkowski.lean) |

**1.2 The Sobolev inequality**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Proposition 1.4 | Sobolev inequality (p = 1, sharp) | `PDE.sobolev_inequality_sharp_p_one` | [`Ch1Statements/SobolevSharpOne.lean`](Ch1Statements/SobolevSharpOne.lean) |
| Proposition 1.5 | Sobolev inequality, 1 ≤ p < d | `PDE.exists_sobolev_constant` | [`SobolevStatements/Sobolev.lean`](SobolevStatements/Sobolev.lean) |
| Lemma 1.6 | Affine normalization of convex domains | `PDE.exists_affine_normalization` | — |
| Lemma 1.7 | Riesz potential bound on convex domains | `PDE.abs_sub_integralAverage_ae_le_riesz` | — |
| Lemma 1.8 | Weak-type bound for the Riesz potential | `PDE.volume_setOf_le_rieszLIntegralOne`<br>`PDE.volume_setOf_le_rieszPotentialOne` | — |
| Theorem 1.9 | Sobolev–Poincaré inequality on convex domains | `PDE.exists_convexSobolevPoincare_constant` | [`SobolevStatements/ConvexSobolevPoincare.lean`](SobolevStatements/ConvexSobolevPoincare.lean) |
| Proposition 1.10 | Poincaré inequality | `PDE.exists_poincare_adjustmean_constant` | [`Ch1Statements/PoincareAdjustMean.lean`](Ch1Statements/PoincareAdjustMean.lean) |
| Lemma 1.12 | Bombieri-Giusti lemma | `PDE.Bombieri.bombieri_giusti` | — |
| Lemma 1.13 | Bombieri lemma | `PDE.exists_bombieri_bound` | [`Ch1Statements/Bombieri.lean`](Ch1Statements/Bombieri.lean) |
| Lemma 1.14 | Vitali covering lemma | [`PDEFoundation/Measure/CompactBallCoverEstimate.lean`](PDEFoundation/Measure/CompactBallCoverEstimate.lean)<br>[`PDEFoundation/Measure/BallMaximalWeak.lean`](PDEFoundation/Measure/BallMaximalWeak.lean) | — |
| Lemma 1.15 | Weak-type maximal inequality | `PDE.volume_set_lt_uncenteredBallMaximal_le` | — |
| Lemma 1.16 | John–Nirenberg inequality on cubes | [`PDEFoundation/Analysis/Inequalities/JohnNirenberg/Cube.lean`](PDEFoundation/Analysis/Inequalities/JohnNirenberg/Cube.lean)<br>[`PDEFoundation/Analysis/Inequalities/JohnNirenberg/CubeClosed.lean`](PDEFoundation/Analysis/Inequalities/JohnNirenberg/CubeClosed.lean) | — |
| Proposition 1.17 | John–Nirenberg inequality | `PDE.exists_johnNirenberg_constant` | [`Ch1Statements/JohnNirenberg.lean`](Ch1Statements/JohnNirenberg.lean) |
| Proposition 1.18 | Trudinger inequality | `PDE.exists_trudinger_constant` | [`Ch1Statements/Trudinger.lean`](Ch1Statements/Trudinger.lean) |
| Lemma 1.19 | Campanato characterization of Hölder spaces | `PDE.exists_campanato_characterization_constant` | [`Ch1Statements/Campanato.lean`](Ch1Statements/Campanato.lean) |
| Lemma 1.20 | Hölder continuity from oscillation decay | `PDE.exists_holderRepresentative_of_essOsc_decay` | [`HoleFillingStatements/OscillationHolder.lean`](HoleFillingStatements/OscillationHolder.lean) |
| Proposition 1.21 | Gaussian Poincaré inequality | `PDE.gaussian_poincare` | [`Ch1Statements/GaussianPoincare.lean`](Ch1Statements/GaussianPoincare.lean) |
| Proposition 1.22 | Nash inequality | `PDE.exists_nash_constant` | [`Ch1Statements/Nash.lean`](Ch1Statements/Nash.lean) |

**1.3 Trace inequalities**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Theorem 1.23 | Trace inequality | `PDE.trace_inequality` | [`Ch1Statements/TraceInequality.lean`](Ch1Statements/TraceInequality.lean) |
| Theorem 1.25 | Right inverse for the trace | `PDE.trace_right_inverse` | [`Ch1Statements/TraceRightInverse.lean`](Ch1Statements/TraceRightInverse.lean) |
| Corollary 1.26 | Characterization of the trace space | `PDE.trace_space_characterization` | [`Ch1Statements/TraceCharacterization.lean`](Ch1Statements/TraceCharacterization.lean) |

### Chapter 2. The Laplace equation


**2.1 Harmonic functions**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Proposition 2.1 | Pointwise derivative bounds for harmonic functions | `PDE.exists_harmonic_pointwise_derivative_bound` | [`HarmonicStatements/Pointwise.lean`](HarmonicStatements/Pointwise.lean) |

**2.2 Monotonicity formulas**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Theorem 2.2 | Almgren monotonicity formula | `PDE.almgren_monotonicity` | [`Ch2Statements/AlmgrenMonotonicity.lean`](Ch2Statements/AlmgrenMonotonicity.lean) |
| Corollary 2.3 | Three sphere theorem | `PDE.three_spheres` | [`Ch2Statements/ThreeSpheres.lean`](Ch2Statements/ThreeSpheres.lean) |
| Lemma 2.8 | Growth of the mean square of a harmonic function over balls | `PDE.mono_sq_balls` | [`Ch2Statements/MonoSqBalls.lean`](Ch2Statements/MonoSqBalls.lean) |
| Corollary 2.9 | Growth estimate from frequency | `PDE.growth_from_frequency`<br>`PDE.entire_harmonic_polynomial_of_frequency_bound` | [`Ch2Statements/GrowthFromFrequency.lean`](Ch2Statements/GrowthFromFrequency.lean)<br>[`Ch2Statements/EntireHarmonicPolynomial.lean`](Ch2Statements/EntireHarmonicPolynomial.lean) |
| Lemma 2.11 | Friedland-Hayman inequality | `PDE.friedland_hayman`<br>`PDE.friedland_hayman_of_disjoint` | [`Ch2Statements/FriedlandHayman.lean`](Ch2Statements/FriedlandHayman.lean)<br>[`Ch2Statements/FriedlandHaymanOfDisjoint.lean`](Ch2Statements/FriedlandHaymanOfDisjoint.lean) |
| Theorem 2.13 | Alt-Caffarelli-Friedman monotonicity formula | `PDE.alt_caffarelli_friedman` | [`Ch2Statements/AltCaffarelliFriedman.lean`](Ch2Statements/AltCaffarelliFriedman.lean) |

**2.3 The heat equation**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Theorem 2.15 | Poon's parabolic frequency function | `PDE.poon_monotonicity` | [`Ch2Statements/PoonMonotonicity.lean`](Ch2Statements/PoonMonotonicity.lean) |

### Chapter 3. Perturbative estimates


**3.1 Schauder estimates**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Proposition 3.1 | `C^{0,1-}` Schauder estimate | `PDE.exists_schauderCalpha_constant` | [`SchauderStatements/Calpha.lean`](SchauderStatements/Calpha.lean) |
| Corollary 3.2 | `C^{0,1-}` estimate for continuous coefficients | `PDE.exists_continuousCoefficientCalpha_constant` | [`SchauderStatements/ContinuousCoefficients.lean`](SchauderStatements/ContinuousCoefficients.lean) |
| Proposition 3.3 | `C^{1,1-}` Schauder estimate | `PDE.exists_schauderC1alpha_constant` | [`SchauderStatements/C1alpha.lean`](SchauderStatements/C1alpha.lean) |

**3.2 Calderón-Zygmund estimates**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Proposition 3.4 | Calderón-Zygmund estimate | `PDE.exists_calderonZygmund`<br>`PDE.exists_unitBall_divergence_representation` | [`CZStatements/General.lean`](CZStatements/General.lean)<br>[`CZStatements/NegativeSobolev.lean`](CZStatements/NegativeSobolev.lean) |
| Lemma 3.5 | Harmonic comparison | `PDE.centeredVectorMeanL2_weakLaplacian_retained_excess_zeroExtension`<br>`PDE.centeredVectorMeanL2_weakLaplacian_retained_excess` | — |
| Lemma 3.6 | Oscillation decomposition | `PDE.exists_sparse_oscillation_decomposition` | — |
| Lemma 3.7 | Local Laplacian estimate | `PDE.exists_localLaplacianLp_constants` | — |
| Proposition 3.8 | Coefficients close to the identity | `PDE.exists_calderonZygmund_identity` | [`CZStatements/Identity.lean`](CZStatements/Identity.lean) |
| Example 3.10 | The oscillation threshold | `PDE.exists_planar_radialMode_sharpness` | [`CZStatements/OscillationSharpness.lean`](CZStatements/OscillationSharpness.lean) |
| Example 3.11 | The forcing constant | `PDE.exists_planar_logarithmic_forcing_sharpness` | [`CZStatements/ForcingSharpness.lean`](CZStatements/ForcingSharpness.lean) |
| Proposition 3.12 | Yudovich uniqueness for the 2d Euler equations | `PDE.yudovich_uniqueness` | [`EulerStatements/YudovichUniqueness.lean`](EulerStatements/YudovichUniqueness.lean) |
| Lemma 3.14 | Periodic Calderón–Zygmund estimate | `PDE.exists_torus_cz` | — |

**Weak-type (1,1) endpoint for the Newtonian potential**

These statements concern the Newtonian potential `u_F` of a vector field `F` and its analogue for a constant symmetric elliptic matrix. They support Section 3.2 and are not numbered results of the manuscript.

| Result | Lean declaration | Statement file |
|---|---|---|
| Newtonian kernel: derivative off the origin | `PDE.newtonKernel_hasFDerivAt` | [`CZStatements/WeakType/NewtonKernelDeriv.lean`](CZStatements/WeakType/NewtonKernelDeriv.lean) |
| Newtonian kernel: Hölder bound for the gradient | `PDE.newtonKernelJacobian_holder` | [`CZStatements/WeakType/NewtonKernelHolder.lean`](CZStatements/WeakType/NewtonKernelHolder.lean) |
| Newtonian potential of a smooth compactly supported field is smooth | `PDE.contDiff_newtonPotential_and_coordDeriv` | [`CZStatements/WeakType/NewtonPotentialSmooth.lean`](CZStatements/WeakType/NewtonPotentialSmooth.lean) |
| Representation of smooth compactly supported solutions of `Δw = div F` | `PDE.eq_newtonPotential_of_laplacian_eq_div` | [`CZStatements/WeakType/NewtonRepresentation.lean`](CZStatements/WeakType/NewtonRepresentation.lean) |
| Local weak-type (1,1) estimate for the gradient of the Newtonian potential | `PDE.exists_newtonPotential_weakTypeOne` | [`CZStatements/WeakType/NewtonWeakType.lean`](CZStatements/WeakType/NewtonWeakType.lean) |
| Constant-matrix potential: linearity | `PDE.newtonPotentialMat_linearCombination` | [`CZStatements/WeakType/NewtonMatPotentialLinear.lean`](CZStatements/WeakType/NewtonMatPotentialLinear.lean) |
| Constant-matrix potential: smoothness and coordinate derivatives | `PDE.contDiff_newtonPotentialMat_and_coordDeriv` | [`CZStatements/WeakType/NewtonMatPotentialSmooth.lean`](CZStatements/WeakType/NewtonMatPotentialSmooth.lean) |
| Representation of smooth compactly supported solutions of `div(M∇w) = div F` | `PDE.eq_newtonPotentialMat_of_div_eq_div` | [`CZStatements/WeakType/NewtonMatRepresentation.lean`](CZStatements/WeakType/NewtonMatRepresentation.lean) |
| Local weak-type (1,1) estimate for the constant-matrix potential | `PDE.exists_newtonPotentialMat_weakTypeOne` | [`CZStatements/WeakType/NewtonMatWeakType.lean`](CZStatements/WeakType/NewtonMatWeakType.lean) |

### Chapter 4. Scale-invariant estimates


**4.1 The hole-filling estimate**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Lemma 4.1 | Caccioppoli inequality | `PDE.DGNM.caccioppoli_positivePart`<br>`PDE.caccioppoli_ball_positivePart_gradient`<br>`PDE.caccioppoli_coefficient_energy_on_inner` | — |
| Lemma 4.2 | Hole-filling estimate | `PDE.exists_holeFilling_constant` | [`HoleFillingStatements/HoleFilling.lean`](HoleFillingStatements/HoleFilling.lean) |
| Proposition 4.3 | Hölder regularity in d = 2 | `PDE.exists_planarHolder_constant` | [`HoleFillingStatements/PlanarHolder.lean`](HoleFillingStatements/PlanarHolder.lean) |

**4.2 Higher integrability and the Meyers estimate**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Theorem 4.4 | Meyers estimate | `PDE.exists_meyers_constants` | [`MeyersStatements/Meyers.lean`](MeyersStatements/Meyers.lean) |
| Lemma 4.5 | Reverse Hölder inequality with Λ^{1/2} contrast dependence | `PDE.meyers_rh_interior_final`<br>`PDE.meyers_rh_boundary_final` | — |
| Lemma 4.6 | Quantitative Gehring lemma | `PDE.exists_gehring_constant` | [`MeyersStatements/Gehring.lean`](MeyersStatements/Gehring.lean) |
| Proposition 4.7 | Sharpness of the range of exponents in Theorem 4.4 | `PDE.meyers_sharpness_example`<br>`PDE.meyers_range_upper_bound`<br>`PDE.meyers_range_upper_bound_dirichlet` | [`Ch4Statements/MeyersSharpnessExample.lean`](Ch4Statements/MeyersSharpnessExample.lean)<br>[`Ch4Statements/MeyersRangeUpperBound.lean`](Ch4Statements/MeyersRangeUpperBound.lean)<br>[`Ch4Statements/MeyersRangeUpperBoundDirichlet.lean`](Ch4Statements/MeyersRangeUpperBoundDirichlet.lean) |

**4.3 The De Giorgi-Nash Hölder estimate**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Theorem 4.8 | Interior Hölder regularity (De Giorgi) | `PDE.exists_deGiorgi_holder_constant` | [`DGNMStatements/DeGiorgiHolder.lean`](DGNMStatements/DeGiorgiHolder.lean) |
| Proposition 4.9 | L^∞ estimate for subsolutions (De Giorgi) | `PDE.exists_localMaxPrinciple_constant` | [`DGNMStatements/LocalMaxPrinciple.lean`](DGNMStatements/LocalMaxPrinciple.lean) |
| Lemma 4.10 | Positive part of a subsolution minus a constant is subharmonic | `PDE.DGNM.subharmonicOn_positivePartSubConst` | — |
| Proposition 4.11 | Expansion of positivity | `PDE.exists_expansionOfPositivity_constant` | [`DGNMStatements/ExpansionOfPositivity.lean`](DGNMStatements/ExpansionOfPositivity.lean) |
| Proposition 4.12 | Lower bound Λ^{(d-1)/4} for the exponent in Proposition 4.9 | `PDE.localmax_lower_example`<br>`PDE.localmax_exponent_lower_bound` | [`Ch4Statements/LocalmaxLowerExample.lean`](Ch4Statements/LocalmaxLowerExample.lean)<br>[`Ch4Statements/LocalmaxExponentLowerBound.lean`](Ch4Statements/LocalmaxExponentLowerBound.lean) |

**4.4 Moser iteration**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Proposition 4.13 | L^∞ estimate for subsolutions (Moser) | `PDE.exists_moserLocalMax_constant` | [`DGNMStatements/MoserLocalMax.lean`](DGNMStatements/MoserLocalMax.lean) |
| Proposition 4.14 | Weak Harnack-type inequality for positive supersolutions, d ≥ 3 | `PDE.exists_weakHarnack0_constant` | [`DGNMStatements/WeakHarnack0.lean`](DGNMStatements/WeakHarnack0.lean) |
| Proposition 4.15 | Expansion of positivity for small θ | `PDE.expansion_small` | [`Ch4Statements/ExpansionSmall.lean`](Ch4Statements/ExpansionSmall.lean) |
| Proposition 4.16 | Crossover estimate | `PDE.exists_crossover_constants` | [`DGNMStatements/Crossover.lean`](DGNMStatements/Crossover.lean) |
| Proposition 4.17 | Weak Harnack inequality | `PDE.exists_weakHarnack_constant` | [`DGNMStatements/WeakHarnack.lean`](DGNMStatements/WeakHarnack.lean) |
| Theorem 4.18 | Harnack inequality | `PDE.exists_harnack_constant` | [`DGNMStatements/Harnack.lean`](DGNMStatements/Harnack.lean) |
| Proposition 4.20 | Sharpness of the Harnack inequality | `PDE.harnack_sharp_example`<br>`PDE.harnack_constant_lower_bound`<br>`PDE.harnack_exponent_lower_bound`<br>`PDE.harnack_constant_ge_one` | [`Ch4Statements/HarnackSharpExample.lean`](Ch4Statements/HarnackSharpExample.lean)<br>[`Ch4Statements/HarnackConstantLowerBound.lean`](Ch4Statements/HarnackConstantLowerBound.lean)<br>[`Ch4Statements/HarnackExponentLowerBound.lean`](Ch4Statements/HarnackExponentLowerBound.lean)<br>[`Ch4Statements/HarnackConstantGeOne.lean`](Ch4Statements/HarnackConstantGeOne.lean) |
| Theorem 4.21 | Interior Hölder regularity (Moser) | `PDE.exists_moser_holder_constant` | [`DGNMStatements/MoserHolder.lean`](DGNMStatements/MoserHolder.lean) |
| Proposition 4.22 | Lower bound for the density estimate | `PDE.cosh_lower_example`<br>`PDE.cosh_lower_consequence` | [`Ch4Statements/CoshLowerExample.lean`](Ch4Statements/CoshLowerExample.lean)<br>[`Ch4Statements/CoshLowerConsequence.lean`](Ch4Statements/CoshLowerConsequence.lean) |

**4.5 The sharp exponent in two dimensions**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Lemma 4.23 | Wirtinger inequality | `PDE.wirtinger_inequality` | [`Ch4Statements/WirtingerInequality.lean`](Ch4Statements/WirtingerInequality.lean) |
| Theorem 4.24 | Piccinini and Spagnolo | `PDE.piccinini_spagnolo_monotonicity` | [`Ch4Statements/PiccininiSpagnoloMonotonicity.lean`](Ch4Statements/PiccininiSpagnoloMonotonicity.lean) |
| Lemma 4.25 | Morrey's Dirichlet growth theorem | `PDE.exists_morrey_growth_constant` | [`Ch4Statements/ExistsMorreyGrowthConstant.lean`](Ch4Statements/ExistsMorreyGrowthConstant.lean) |
| Proposition 4.26 | Meyers' example | `PDE.meyers_example` | [`Ch4Statements/MeyersExample.lean`](Ch4Statements/MeyersExample.lean) |
| Proposition 4.27 | Sharp Hölder exponent in d = 2 | `PDE.exists_sharp2d_holder_constant`<br>`PDE.sharp2d_not_holder` | [`Ch4Statements/ExistsSharp2dHolderConstant.lean`](Ch4Statements/ExistsSharp2dHolderConstant.lean)<br>[`Ch4Statements/Sharp2dNotHolder.lean`](Ch4Statements/Sharp2dNotHolder.lean) |

**4.6 Sharpness of the Hölder exponent and of the Harnack ratio for $d\geq3$**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Proposition 4.30 | Sharpness of the Hölder exponent and Harnack ratio, d ≥ 3 | `PDE.guerra_sharp_example`<br>`PDE.guerra_sharp_example_nonsymmetric` | [`GuerraStatements/SharpExample.lean`](GuerraStatements/SharpExample.lean)<br>[`GuerraStatements/SharpExampleNonsymmetric.lean`](GuerraStatements/SharpExampleNonsymmetric.lean) |
| Lemma 4.31 | Symmetrization of a flux | `PDE.guerra_symmetrize` | [`GuerraStatements/Symmetrize.lean`](GuerraStatements/Symmetrize.lean) |
| Corollary 4.32 | Sharp order of the Hölder exponent and the Harnack constant | `PDE.guerra_harnack_sharp` | [`GuerraStatements/HarnackSharp.lean`](GuerraStatements/HarnackSharp.lean) |

**4.7 Green function decay estimates**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Lemma 4.33 | Dirichlet problem | `PDE.greenDirichlet` | [`Ch4Statements/GreenDirichlet.lean`](Ch4Statements/GreenDirichlet.lean) |
| Lemma 4.34 | Weak maximum principle | `PDE.greenMaxPrinciple` | [`Ch4Statements/GreenMaxPrinciple.lean`](Ch4Statements/GreenMaxPrinciple.lean) |
| Lemma 4.35 | Green function decay from oscillation decay | `PDE.greenDecay` | [`Ch4Statements/GreenDecay.lean`](Ch4Statements/GreenDecay.lean) |
| Corollary 4.36 | Measurable coefficients | `PDE.greenDecayDGN` | [`Ch4Statements/GreenDecayDGN.lean`](Ch4Statements/GreenDecayDGN.lean) |
| Corollary 4.37 | Constant coefficients | `PDE.greenDecayConst` | [`Ch4Statements/GreenDecayConst.lean`](Ch4Statements/GreenDecayConst.lean) |
| Lemma 4.38 | Value at the pole | [`EllipticRegularity/Ch4/GreenFunction/Pole.lean`](EllipticRegularity/Ch4/GreenFunction/Pole.lean) | — |
| Definition 4.39 | Green function | `PDE.IsGreenFunction` | — |
| Proposition 4.40 | Existence and basic properties of the Green function | `PDE.greenExists` | [`Ch4Statements/GreenExists.lean`](Ch4Statements/GreenExists.lean) |
| Lemma 4.41 | Harnack inequality in annuli | `PDE.Ch4GreenHarnack.harnack_annulus` | — |
| Proposition 4.42 | Green function estimates, d ≥ 3 | `PDE.greenD3` | [`Ch4Statements/GreenD3.lean`](Ch4Statements/GreenD3.lean) |

### Chapter 5. Parabolic equations


**5.1 Function spaces for parabolic equations**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Definition 5.1 | The space H¹_par | `PDE.ParH1Function`<br>`PDE.ParCutoff`<br>`PDE.IsL2c` | — |
| Definition 5.4 | Weak solutions, sub- and supersolutions (parabolic) | `PDE.IsParabolicWeakSolution`<br>`PDE.IsParabolicCoeff`<br>`PDE.ParTestFunction` | — |
| Lemma 5.5 | Weak formulation at every time | `PDE.parabWeakSlice` | [`Ch5Statements/WeakSlice.lean`](Ch5Statements/WeakSlice.lean) |
| Lemma 5.6 | Energy identity | `PDE.parabEnergy` | [`Ch5Statements/Energy.lean`](Ch5Statements/Energy.lean) |

**5.2 Parabolic Caccioppoli inequality**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Lemma 5.8 | Caccioppoli inequality, parabolic version | `PDE.parabCaccioppoli` | [`Ch5Statements/Caccioppoli.lean`](Ch5Statements/Caccioppoli.lean) |
| Lemma 5.10 | Time slice estimate | `PDE.parabSliceEstimate` | [`Ch5Statements/SliceEstimate.lean`](Ch5Statements/SliceEstimate.lean) |

**5.3 The Nash-Aronson estimate**

| No. | Result | Lean declaration | Statement file |
|---|---|---|---|
| Proposition 5.11 | Nash-Aronson upper bound | `PDE.nashAronsonUpper` | [`Ch5NashStatements/NashUpper.lean`](Ch5NashStatements/NashUpper.lean) |
| Proposition 5.12 | On-diagonal lower bound | `PDE.onDiagLower` | [`Ch5NashStatements/OnDiagLower.lean`](Ch5NashStatements/OnDiagLower.lean) |
| Proposition 5.13 | Parabolic weak Harnack inequality | `PDE.parabWeakHarnack` | [`Ch5NashStatements/WeakHarnack.lean`](Ch5NashStatements/WeakHarnack.lean) |
| Corollary 5.14 | Parabolic Harnack inequality | `PDE.parabLocalHarnack` | [`Ch5NashStatements/LocalHarnack.lean`](Ch5NashStatements/LocalHarnack.lean) |
| Theorem 5.15 | Nash-Aronson lower bound | `PDE.nashAronsonLower` | [`Ch5NashStatements/NashLower.lean`](Ch5NashStatements/NashLower.lean) |

**5.3 Supporting statements**

Standard facts about the Cauchy problem on `ℝ^d × [s,T]` and the kernel form of the Nash-Aronson estimate, used in Section 5.3. They are not numbered results of the manuscript.

| Result | Lean declaration | Statement file |
|---|---|---|
| Time reversal and transposition preserve the parabolic coefficient class | `PDE.parAdjCoeff_isParabolicCoeff` | [`Ch5NashStatements/CauchyAdjCoeff.lean`](Ch5NashStatements/CauchyAdjCoeff.lean) |
| Adjoint duality for the Cauchy problem | `PDE.cauchyDuality` | [`Ch5NashStatements/CauchyDuality.lean`](Ch5NashStatements/CauchyDuality.lean) |
| Energy identity for the Cauchy problem | `PDE.cauchyEnergyIdentity` | [`Ch5NashStatements/CauchyEnergy.lean`](Ch5NashStatements/CauchyEnergy.lean) |
| Existence for the Cauchy problem | `PDE.cauchyExistence` | [`Ch5NashStatements/CauchyExistence.lean`](Ch5NashStatements/CauchyExistence.lean) |
| `L¹` contraction | `PDE.cauchyL1Contraction` | [`Ch5NashStatements/CauchyL1.lean`](Ch5NashStatements/CauchyL1.lean) |
| Mass conservation | `PDE.cauchyMass` | [`Ch5NashStatements/CauchyMass.lean`](Ch5NashStatements/CauchyMass.lean) |
| Positivity of the Cauchy evolution | `PDE.cauchyPositivity` | [`Ch5NashStatements/CauchyPositivity.lean`](Ch5NashStatements/CauchyPositivity.lean) |
| Uniqueness for the Cauchy problem | `PDE.cauchyUniqueness` | [`Ch5NashStatements/CauchyUniqueness.lean`](Ch5NashStatements/CauchyUniqueness.lean) |
| Kernel form of the Nash-Aronson estimate | `PDE.nashAronsonKernel` | [`Ch5NashStatements/NashKernel.lean`](Ch5NashStatements/NashKernel.lean) |
