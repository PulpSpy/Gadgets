use ark_ec::pairing::Pairing;
use ark_ff::FftField;
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, Evaluations, Radix2EvaluationDomain};

pub struct ConstraintPoly<F: FftField> {
    pub numerator: DensePolynomial<F>,
    pub quotient: DensePolynomial<F>,
}

impl<F: FftField> ConstraintPoly<F> {
    pub fn new(numerator: DensePolynomial<F>, quotient: DensePolynomial<F>) -> Self {
        Self { numerator, quotient }
    }
}

pub struct WitnessPolys<F: FftField> {
    pub pa: DensePolynomial<F>,
    pub pb: DensePolynomial<F>,
}

impl<F: FftField> WitnessPolys<F> {
    pub fn new(pa: DensePolynomial<F>, pb: DensePolynomial<F>) -> Self {
        Self { pa, pb }
    }
}

pub fn build_witness_polys<E: Pairing>(
    domain: Radix2EvaluationDomain<E::ScalarField>,
    values: &[u64],
) -> WitnessPolys<E::ScalarField> {
    let degree = values.len();
    let domain_size = domain.size() as usize;

    let mut a_evals: Vec<E::ScalarField> = values
        .iter()
        .copied()
        .map(E::ScalarField::from)
        .collect();

    a_evals.extend(vec![E::ScalarField::from(1u64); domain_size - degree]);

    let pa = Evaluations::from_vec_and_domain(a_evals.clone(), domain).interpolate();

    let _ = pa;
    todo!("next step: compute pb from accumulator evaluations");
}


