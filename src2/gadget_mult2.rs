use ark_ff::FftField;
use ark_poly::univariate::DensePolynomial;

#[allow(non_camel_case_types)]
struct gadget_mult2<F: FftField> {
    pa: DensePolynomial<F>,
    pb: DensePolynomial<F>,
    q_transition: DensePolynomial<F>,
    q_boundary: DensePolynomial<F>,
}
