//! Standalone implementation of a `mult2`-style polynomial IOP gadget.
//! This mirrors the learning-oriented mult2 pattern from Plonkbook:
//! https://plonkbook.org/docs/gadgets/mult2/


use ark_bls12_381::Fr;
use ark_ff::{One, Zero};
use ark_poly::{
    univariate::{DenseOrSparsePolynomial, DensePolynomial},
    DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain,
};

fn suffix_product_accumulator(evals: &[Fr]) -> Vec<Fr> {
    let len = evals.len();
    let mut acc = vec![Fr::zero(); len];
    acc[len - 1] = evals[len - 1];
    for i in (0..len - 1).rev() {
        acc[i] = acc[i + 1] * evals[i];
    }
    acc
}

fn main() {
    // Demo inputs: prove their product is encoded by the accumulator polynomial.
    let values: Vec<u64> = vec![2, 3, 5, 7];
    let degree = values.len();
    let domain_size = degree.next_power_of_two();
    let domain = Radix2EvaluationDomain::<Fr>::new(domain_size).expect("unsupported domain size");

    // P_A evaluations: input values padded with 1s to fill the domain.
    let mut a_evals: Vec<Fr> = values.iter().map(|v| Fr::from(*v)).collect();
    a_evals.extend(vec![Fr::one(); domain_size - degree]);

    // P_B evaluations: suffix-product accumulator.
    let b_evals = suffix_product_accumulator(&a_evals);
    let mut b_shifted_evals = b_evals.clone();
    b_shifted_evals.rotate_left(1);

    // Interpolate witness polynomials.
    let pa = Evaluations::from_vec_and_domain(a_evals.clone(), domain).interpolate();
    let pb = Evaluations::from_vec_and_domain(b_evals, domain).interpolate();
    let pb_shifted = Evaluations::from_vec_and_domain(b_shifted_evals, domain).interpolate();

    // Constraint 1 (transition):
    // [P_B(X) - P_B(Xw) * P_A(X)] * (X - w^{n-1}) = Z_H(X) * Q_transition(X)
    let last_root = domain.element(domain_size - 1);
    let x_minus_last_root =
        DensePolynomial::<Fr>::from_coefficients_vec(vec![-last_root, Fr::one()]);
    let vanishing = DenseOrSparsePolynomial::from(domain.vanishing_polynomial());

    let mut transition_numerator = &pb_shifted * &pa;
    transition_numerator = &pb - &transition_numerator;
    transition_numerator = &transition_numerator * &x_minus_last_root;

    let (q_transition, transition_remainder) =
        DenseOrSparsePolynomial::from(transition_numerator)
            .divide_with_q_and_r(&vanishing)
            .expect("transition division should succeed");
    assert!(transition_remainder.is_zero());

    // Constraint 2 (boundary):
    // P_A(X) - P_B(X) = (X - w^{degree-1}) * Q_boundary(X)
    let degree_root = domain.element(degree - 1);
    let x_minus_degree_root = DenseOrSparsePolynomial::from(
        DensePolynomial::<Fr>::from_coefficients_vec(vec![-degree_root, Fr::one()]),
    );
    let boundary_numerator = DenseOrSparsePolynomial::from(&pa - &pb);
    let (q_boundary, boundary_remainder) = boundary_numerator
        .divide_with_q_and_r(&x_minus_degree_root)
        .expect("boundary division should succeed");
    assert!(boundary_remainder.is_zero());

    // Product check: P_B(1) equals product of original (unpadded) values.
    let claimed_product: Fr = values.iter().map(|v| Fr::from(*v)).product();
    let opened_product = pb.evaluate(&Fr::one());
    assert_eq!(claimed_product, opened_product);

    println!("input values: {:?}", values);
    println!("claimed product: {}", claimed_product);
    println!("opened product P_B(1): {}", opened_product);
    println!("transition quotient degree: {}", q_transition.degree());
    println!("boundary quotient degree: {}", q_boundary.degree());
    println!("all checks passed");
}
