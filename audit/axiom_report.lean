/- # Axiom certificate — the golden `#print axioms` trace.

   The formalization-assurance *Verification* axis: the kernel facts behind each headline,
   generated (never hand-authored) so README / `AXIOM_AUDIT.md` counts can be diffed against it.

   Regenerate / check:  `bash audit/gen_axiom_report.sh`  (writes / diffs `audit/axiom-report.txt`). -/
import SeibergWitten
import RiemannPeriods.Basic

open SeibergWitten SeibergWitten.Physics SeibergWitten.Physics.SU2

-- Proved mathematical spine (genus_swCurve / sw_metric_posDef moved to the unbuilt
-- HigherGenus/ layer with the jacobian-challenge decoupling, 2026-07-06)

-- Headline: existence & uniqueness up to duality
#print axioms sw_effective_theory_unique_up_to_duality    -- std-3 + periodRigidityAxiom
#print axioms sw_unique_up_to_duality                     -- std-3 + periodRigidityAxiom
#print axioms sw_curve_admits_effective_theory            -- std-3 + periodRigidityAxiom

-- SU(2) uniqueness: classical-analysis axioms + the one physical axiom
#print axioms sw_su2_unique  -- + AX_thrice_punctured_uniformization, AX_developing_map_rigidity (SameSWMonodromy: demoted to a def 2026-07-04 — no physics axiom)

-- EFT beta function: its own weak-coupling asymptotic axiom (off the headline footprint)
#print axioms betaFunction_weakCoupling                  -- standard-3 (log-running input DISCHARGED 2026-07-05 by explicit witness)
#print axioms periodRatio_logDeriv_asymptotic             -- standard-3 (was an axiom; purely existential, Ein-witness)

-- Matter Argyres–Douglas: DISCHARGED 2026-07-06 (constructed witness, MatterChart.lean)
#print axioms matter_argyresDouglasLocus_nonempty         -- standard-3 (was: + matterPeriodRigidityAxiom)
#print axioms swCurveMatter_nf1_ad                        -- standard-3
#print axioms not_isCuspOf_nf0                            -- standard-3

-- Genus-1 period engine, dictionary bridge, and the H5 non-vacuity witness (all standard-3)
#print axioms swLambda_deriv_eq_half_period
#print axioms dualityFrame_of_periodFrame
#print axioms hasFiniteOrderAutomorphism_of_neg_invariant
#print axioms RiemannPeriods.tau_im_pos

-- C-route (rank-1 program): C1h holomorphy PROVED (std-3); the developing-map candidate
-- is holomorphic from C1h + C1's nonvanishing only
#print axioms ellipticKm_differentiableOn                 -- standard-3
#print axioms ellipticEm_differentiableOn                 -- standard-3
#print axioms tau_ratio_differentiableOn                  -- std-3 + AX_elliptic_inversion

-- C-route closure at the coupling level: the SU(2) coupling exists (explicit elliptic
-- construction) and is unique up to a Gamma(2) duality frame — classical axioms only
#print axioms su2_coupling_exists                         -- std-3 + AX_elliptic_inversion
#print axioms su2_coupling_canonical  -- + AX_thrice_punctured_uniformization, AX_developing_map_rigidity

-- Special-coordinate layer S0: H2's analytic heart — the dual coordinate vanishes at
-- the monopole. AXIOM-FREE since the loop's first discharge iteration (the at-0 cusp
-- limits are now theorems; C3 shrank to the m=1 cusp clauses)
#print axioms swAD_tendsto_zero_monopole                  -- standard-3
#print axioms ellipticKm_tendsto_zero                     -- standard-3 (former C3 clause)
#print axioms ellipticEm_tendsto_zero                     -- standard-3 (former C3 clause)
#print axioms ellipticEm_one                              -- standard-3 (E(1) = 1, computed)
#print axioms ellipticEm_one_sub_tendsto                  -- standard-3 (former C3 clause)
#print axioms ellipticEm_hasDerivAt                       -- standard-3 (Legendre ODE for E)
#print axioms ellipticKm_hasDerivAt                       -- standard-3 (Legendre ODE for K, via IBP)
#print axioms legendreRelation_hasDerivAt_zero            -- standard-3 (C2's Wronskian is critical)
#print axioms legendreL_eq_half                           -- standard-3 (L constant on the cut plane)
#print axioms legendre_relation  -- C2 DISCHARGED twice over: now STANDARD-3 ONLY (C3 axiom deleted 2026-07-05)
#print axioms swA_hasDerivAt                              -- standard-3 (da/du = c K/sqrt(u+L^2))
#print axioms swAD_hasDerivAt                             -- standard-3 (da_D/du = c i K(1-m)/sqrt(u+L^2))
#print axioms swAD_deriv_eq_swTau_mul_swA_deriv           -- S1: da_D/da = swTau (std-3 + AX_elliptic_inversion)
#print axioms swA_weakCoupling                            -- standard-3 (H6 weak coupling: a/sqrt(u+L^2) -> sqrt2/2)
#print axioms ellipticKm_one_sub_ofReal                   -- standard-3 (C3 staging: K(1-x) realized as a real integral)
#print axioms integral_rpow_neg_half_sq_add               -- standard-3 (C3 staging: the model log integral, FTC)
#print axioms cusp_diff_integrand_bound                   -- standard-3 (C3 staging: uniform bound 0 <= diff <= pi^2)
#print axioms cusp_diff_integral_tendsto                  -- standard-3 (C3 staging: dominated convergence of the comparison)
#print axioms cusp_eps_integral                           -- standard-3 (C3 staging: FTC on [eps, pi/2], antiderivative log tan(phi/2) - log phi)
#print axioms cusp_limit_integral_eval                    -- standard-3 (C3 staging: int (1/sin - 1/phi) = log 2 - log(pi/2))
#print axioms cusp_asymptotic_real                        -- standard-3 (C3 assembly: real cusp asymptotic, 2 log 2)
#print axioms elliptic_cusp_limit                         -- C3 DISCHARGED: standard-3 (formerly axiom AX_elliptic_cusp_limits)
-- The modular lambda layer (E11) — trace-coverage added 2026-07-05 after noticing
-- the theta-pair axioms never appeared below despite being consumed here.
#print axioms theta3_neg_inv                              -- theta-null S-law
#print axioms theta2_neg_inv                              -- theta-null S-law
#print axioms modularLambda_add_two                       -- lambda T^2-invariance
#print axioms oneMinusLambda                              -- 1 - lambda = theta4^4/theta3^4 (consumes the theta pair)
#print axioms modularLambda_S                             -- lambda S-law (consumes the theta pair via oneMinusLambda)
#print axioms modularLambda_ST2S                          -- lambda ST^2S^-1-invariance
#print axioms modularLambda_add_one                       -- the T-law (MC3/Q2 fix): lambda(tau+1) = lambda/(lambda-1)
#print axioms matter_coupling_rigidity                    -- MC3 COMPLETE: chart-level matter rigidity (theta pair + covering pair only)
#print axioms matter_frame_alignment                      -- MC3 STAGE B: matter rigidity germ (theta pair + covering pair ONLY)
#print axioms anharmonicWord_lambda                       -- MC3 stage A: lambda(W_i tau) = sigma_i(lambda tau) (std-3 + theta pair)
#print axioms anharmonic_pairwise_ne                      -- standard-3 (MC3/Q1: six branches distinct off E, by computation)
#print axioms eqOn_branch_of_preconnected                 -- standard-3 (MC3 ob.2: finite branch selection is constant)
#print axioms jLambda_eq_anharmonic                       -- standard-3 (MC3 ob.1: jl-fibre = the anharmonic orbit)
#print axioms jLambda_one_sub                             -- standard-3 (MC2: anharmonic invariance, 1 - l)
#print axioms jLambda_inv                                 -- standard-3 (MC2: anharmonic invariance, 1/l)
#print axioms matter_nf1_ad_invariants                    -- standard-3 (MC1: AD point as g2 = g3 = 0, invariant form)
#print axioms quarticG2_of_triple_root                    -- standard-3 (MC1: triple root => g2 = 0, general)
#print axioms multipliable_tripleProductTerm              -- standard-3 (T0: the Jacobi triple product converges)
#print axioms tripleProduct_quasi_periodic                -- standard-3 (T1: qw P(q, q^2 w) = P(q, w))
#print axioms jacobiTripleProduct_ne_zero                 -- standard-3 (T3a: the product is nonzero on the annulus)
#print axioms differentiable_jacobiTripleProduct_exp      -- standard-3 (T2 brick: the product side is entire in z)
#print axioms tau_ratio_hasDerivAt                        -- Wronskian d tau/dm = -i pi/(4m(1-m)K^2) (std-3 + AX_elliptic_inversion)
#print axioms swTau_hasDerivAt                            -- d tau/du = i pi/(4(u+L^2)(1-m)K^2) (std-3 + AX_elliptic_inversion)
#print axioms swTau_logDeriv_weakCoupling                 -- FAITHFUL one-loop log-running: u tau' -> i/pi (std-3 + AX_elliptic_inversion)

-- Singularity count: why exactly one monopole-dyon pair (n = 1) -- zero new axioms
#print axioms SingularityCount.count_mod_twelve           -- standard-3 (the obstruction: counting alone gives n = 1 mod 6; K3 loophole real)
#print axioms SingularityCount.singularity_count_pinch    -- standard-3 (counting + homogeneity pinch => exactly 2 singularities)
#print axioms SingularityCount.sw_exactly_two_singularities' -- standard-3 (pure SU(2), physical I4* frame: n = 1)
#print axioms SingularityCount.sw_singular_values         -- standard-3 (the pair is exactly {L^2, -L^2})

-- Developing base derived: the monodromy postulate demoted to a theorem
#print axioms SU2.entire_polynomial_of_growth          -- standard-3 (polynomial-growth Liouville, dslope induction)
#print axioms SU2.swModulusData_eq_crossRatio          -- standard-3 (qualitative cusp data => the pinned developing formula, incl. normalization)
#print axioms SU2.swModulusData_swCrossRatio           -- standard-3 (non-vacuity: the cross-ratio carries the data)
#print axioms SU2.sw_su2_unique_of_modulusData         -- covering pair only (decomposed headline: cusp data replaces the pinned formula)

-- Cusp-data campaign step C: the omitted values cost no physics
#print axioms modularLambdaFn_ne_one                      -- theta pair only (lambda misses 1 on H)
#print axioms modularLambdaFn_ne_zero                     -- theta pair only (S-law swaps the omitted values)

-- Cusp-data campaign step A: the lambda-frame SW monodromies
#print axioms SU2.swM_factorization                       -- standard-3 (M_infty = M_mono * M_dyon)
#print axioms SU2.swMMono_mem_Gamma2                      -- standard-3 (all three in Gamma(2); -I in Gamma(2) at level 2)
#print axioms SU2.modularLambda_swMMono                   -- theta pair only (lambda-invariance of the monopole action)
#print axioms SU2.modularLambda_swMDyon                   -- theta pair only (dyon action, via ST2S' + T-square laws)

-- Cusp-data campaign step B: monodromy group + atlas descent
#print axioms SU2.moebiusOn_mul                           -- standard-3 (Moebius composition on H; closes the matter plan's optional item)
#print axioms SU2.modularLambda_swMonodromyGroup          -- theta pair only (lambda-invariance for the WHOLE monodromy group, closure induction)
#print axioms SU2.differentiableAt_modularLambdaFn        -- theta pair only (lambda differentiable on H)
#print axioms SU2.atlasModulus_eq                         -- theta pair only (descent: the global J is well-defined)
#print axioms SU2.swModulusData_of_atlas                  -- theta pair only (atlas => half of SWModulusData; the three limits remain for steps D/E)

-- Cusp-data campaign step D2: lambda -> 0 uniformly at the cusp (theta-series estimate)
#print axioms SU2.tendsto_modularLambdaFn_comap_im_atTop  -- theta pair only (no theta2 bound needed: 1-lambda = theta4^4/theta3^4 + shift law)

-- Cusp-data campaign step D1: the cusp dichotomy (no Picard, no max modulus)
#print axioms SU2.cusp_dichotomy                          -- standard-3 (untwisting + Periodic.cuspFunction removability: bounded Im T, or Im T -> infinity uniformly)
#print axioms SU2.cusp_dichotomy_lambda                   -- theta pair only (cusp branch delivers lambda -> 0 via D2)

-- Cusp-data campaign ENDGAME: SWModulusData from atlas + three genuine cusp lifts
#print axioms SU2.swMDyon_trace                           -- standard-3 (parabolicity: the faithfulness check that caught the v1 hyperbolic slip)
#print axioms SU2.IsGenuineCuspLift.lambda_tendsto        -- theta pair only (genuine lift runs to the cusp: dichotomy + D2)
#print axioms SU2.swModulusData_of_atlas_and_lifts        -- theta pair only (H2+H3+H4+H6qual data => ALL of SWModulusData)
#print axioms SU2.sw_su2_unique_coulomb                   -- covering pair only (chart bookkeeping discharged on the maximal domain)

-- AnomalyGraded demoted: derived from the R-spurion covariance of the curve family
#print axioms SingularityCount.anomalyGraded_of_rSpurionCovariant  -- standard-3 (H5+H6 shadow => the grading)
#print axioms SingularityCount.rSpurionCovariant_swG2'             -- standard-3 (non-vacuity, physical frame)

-- H7: spurionic U(1)_R covariance of the Lambda-family (dimensional transmutation + theta-periodicity)
#print axioms instanton_remainder_covariant               -- standard-3 (H6's homogeneity clause as H7's shadow)
#print axioms oneLoopPrepotential_smul                    -- standard-3 (one-loop exactly covariant: log of the invariant ratio)
#print axioms spurionCovariantFamily_classical            -- standard-3 (non-vacuity, zero frame shift)

-- MPRA discharge (Stage A): the first constructed PeriodChart; axiom deleted
#print axioms matterPeriodRigidity_nf1_ad                 -- standard-3 (the former axiom's statement, constructed)
#print axioms monic_quartic_squarefree_iff_disc           -- standard-3 (the quartic discriminant bridge)
#print axioms matter_ad_cusp_unique                       -- standard-3 (the AD point is the unique cusp)
