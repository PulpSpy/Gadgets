use std::ops::Mul;

use ark_ec::pairing::Pairing;
use ark_ff::{FftField, Zero};
use ark_poly::{
    univariate::{DenseOrSparsePolynomial, DensePolynomial},
    DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain,
};
use ark_poly_commit::kzg10::{KZG10, Powers, VerifierKey};
use ark_std::{rand::RngCore, One};

use crate::utils::{batch_check, batch_open, BatchCheckProof, Transcript};

#[allow(non_camel_case_types)]
struct gadget_mult2<F: FftField> {
    pa: DensePolynomial<F>,
    pb: DensePolynomial<F>,
    q_transition: DensePolynomial<F>,
    q_boundary: DensePolynomial<F>,
}

/// Product-check gadget (mult2-style):
/// prove that `values[0] * ... * values[d-1]` is bound to an opened accumulator value.
pub fn prove<E: Pairing, R: RngCore>(
    powers: &Powers<E>,
    values: &Vec<u64>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    rng: &mut R,
) -> BatchCheckProof<E> {
    let witness = build_witness_polynomials::<E>(domain, values);

    let (cm_pa, mask_pa) = KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
        powers,
        &witness.pa,
        Some(witness.pa.degree()),
        Some(rng),
    )
    .unwrap();

    let (cm_pb, mask_pb) = KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
        powers,
        &witness.pb,
        Some(witness.pb.degree()),
        Some(rng),
    )
    .unwrap();

    let (cm_q_transition, mask_q_transition) =
        KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
            powers,
            &witness.q_transition,
            Some(witness.q_transition.degree()),
            Some(rng),
        )
        .unwrap();

    let (cm_q_boundary, mask_q_boundary) = KZG10::<E, DensePolynomial<E::ScalarField>>::commit(
        powers,
        &witness.q_boundary,
        Some(witness.q_boundary.degree()),
        Some(rng),
    )
    .unwrap();

    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_pa.0,
        cm_pb.0,
        cm_q_transition.0,
        cm_q_boundary.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());

    let (h1, open_evals1, gamma1) = batch_open(
        powers,
        &vec![
            &witness.pa,
            &witness.pb,
            &witness.q_transition,
            &witness.q_boundary,
        ],
        &vec![&mask_pa, &mask_pb, &mask_q_transition, &mask_q_boundary],
        zeta,
        false,
        rng,
    );

    let omega = domain.element(1);
    let (h2, open_evals2, gamma2) = batch_open(
        powers,
        &vec![&witness.pb],
        &vec![&mask_pb],
        zeta * omega,
        false,
        rng,
    );

    let (h3, open_evals3, gamma3) = batch_open(
        powers,
        &vec![&witness.pb],
        &vec![&mask_pb],
        E::ScalarField::one(),
        false,
        rng,
    );

    BatchCheckProof {
        commitments: vec![
            vec![cm_pa, cm_pb, cm_q_transition, cm_q_boundary],
            vec![cm_pb],
            vec![cm_pb],
        ],
        witnesses: vec![h1, h2, h3],
        points: vec![zeta, zeta * omega, E::ScalarField::one()],
        open_evals: vec![open_evals1, open_evals2, open_evals3],
        gammas: vec![gamma1, gamma2, gamma3],
    }
}

pub fn verify_product<E: Pairing>(values: &Vec<u64>, proof: &BatchCheckProof<E>) {
    let expected_product: E::ScalarField = values
        .iter()
        .map(|value| E::ScalarField::from(*value))
        .product();
    assert_eq!(expected_product, proof.open_evals[2][0].into_plain_value().0);
}

pub fn verify_evaluations<E: Pairing, R: RngCore>(
    vk: VerifierKey<E>,
    proof: &BatchCheckProof<E>,
    domain: Radix2EvaluationDomain<E::ScalarField>,
    degree: usize,
    rng: &mut R,
) {
    let cm_pa = proof.commitments[0][0];
    let cm_pb = proof.commitments[0][1];
    let cm_q_transition = proof.commitments[0][2];
    let cm_q_boundary = proof.commitments[0][3];

    let mut transcript = Transcript::new();
    transcript.append_affines::<E>(&vec![
        cm_pa.0,
        cm_pb.0,
        cm_q_transition.0,
        cm_q_boundary.0,
    ]);
    let zeta = transcript.append_and_digest::<E>("zeta".to_string());
    assert_eq!(zeta, proof.points[0]);

    let omega = domain.element(1);
    assert_eq!(zeta * omega, proof.points[1]);

    let pa_zeta = proof.open_evals[0][0].into_plain_value().0;
    let pb_zeta = proof.open_evals[0][1].into_plain_value().0;
    let q_transition_zeta = proof.open_evals[0][2].into_plain_value().0;
    let q_boundary_zeta = proof.open_evals[0][3].into_plain_value().0;
    let pb_zeta_omega = proof.open_evals[1][0].into_plain_value().0;

    let zeta_vanishing = domain.vanishing_polynomial().evaluate(&zeta);
    let last_root = domain.element(domain.size as usize - 1);
    let transition_lhs = (pb_zeta - pb_zeta_omega.mul(pa_zeta)) * (zeta - last_root);
    let transition_rhs = zeta_vanishing * q_transition_zeta;
    assert_eq!(transition_lhs, transition_rhs);

    let degree_root = domain.element(degree - 1);
    let boundary_lhs = pa_zeta - pb_zeta;
    let boundary_rhs = q_boundary_zeta * (zeta - degree_root);
    assert_eq!(boundary_lhs, boundary_rhs);

    batch_check(&vk, proof, rng);
}

fn build_witness_polynomials<E: Pairing>(
    domain: Radix2EvaluationDomain<E::ScalarField>,
    values: &Vec<u64>,
) -> gadget_mult2<E::ScalarField> {
    let degree = values.len();
    let domain_size = domain.size as usize;

    let mut a_evals: Vec<E::ScalarField> = values
        .iter()
        .map(|value| E::ScalarField::from(*value))
        .collect();
    a_evals.extend(vec![E::ScalarField::one(); domain_size - degree]);

    let b_evals = suffix_product_accumulator(&a_evals);
    let mut b_shifted_evals = b_evals.clone();
    b_shifted_evals.rotate_left(1);

    let pa = Evaluations::from_vec_and_domain(a_evals, domain).interpolate();
    let pb = Evaluations::from_vec_and_domain(b_evals, domain).interpolate();
    let pb_shifted = Evaluations::from_vec_and_domain(b_shifted_evals, domain).interpolate();

    let last_root = domain.element(domain_size - 1);
    let x_minus_last_root =
        DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![-last_root, E::ScalarField::one()]);
    let vanishing = DenseOrSparsePolynomial::from(domain.vanishing_polynomial());

    // [P_B(X) - P_B(Xw) * P_A(X)] * (X - w^{n-1}) = Z(X) * Q_transition(X)
    let mut transition_numerator = &pb_shifted * &pa;
    transition_numerator = &pb - &transition_numerator;
    transition_numerator = &transition_numerator * &x_minus_last_root;
    let (q_transition, transition_remainder) =
        DenseOrSparsePolynomial::from(transition_numerator)
            .divide_with_q_and_r(&vanishing)
            .unwrap();
    assert!(transition_remainder.is_zero());

    // P_A(X) - P_B(X) = Q_boundary(X) * (X - w^{degree-1})
    let degree_root = domain.element(degree - 1);
    let x_minus_degree_root =
        DenseOrSparsePolynomial::from(DensePolynomial::<E::ScalarField>::from_coefficients_vec(vec![
            -degree_root,
            E::ScalarField::one(),
        ]));
    let boundary_numerator = DenseOrSparsePolynomial::from(&pa - &pb);
    let (q_boundary, boundary_remainder) =
        boundary_numerator.divide_with_q_and_r(&x_minus_degree_root).unwrap();
    assert!(boundary_remainder.is_zero());

    gadget_mult2 {
        pa,
        pb,
        q_transition,
        q_boundary,
    }
}

fn suffix_product_accumulator<F: FftField>(evals: &Vec<F>) -> Vec<F> {
    let len = evals.len();
    let mut acc = vec![F::zero(); len];
    acc[len - 1] = evals[len - 1];
    for i in (0..len - 1).rev() {
        acc[i] = acc[i + 1] * evals[i];
    }
    acc
}
