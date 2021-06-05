/*
 * Specification of matrix-vector multiplication for dense
 * matrices and CSR sparse format, showing refinement
 * using ELL and CSR abstraction functions
 * 
 */

open structure
open behavior

-- a sum of products
sig SumProd {
  vals: Int->lone Value->Value
}

-- dense matrix-vector multiplication
pred MVM [m: Matrix, x: seq Value, b: seq SumProd] {
  m.rows = #b
  m.cols = #x
  all i: range[m.rows] |
    b[i].vals = { j: Int, p, q: Value-Zero |
      j in range[m.cols] and p = m.vals[i][j] and q = x[j] }
}

-- CSR matrix-vector multiplication
pred MVM [c: CSR, x: seq Value, b: seq SumProd] {
  c.rows = #b
  c.cols = #x
  all i: range[c.rows] |
    b[i].vals = { j: Int, p, q: Value-Zero |
      some k: range[c.IA[i], c.IA[i.add[1]]] |
        j = c.JA[k] and p = c.A[k] and q = x[c.JA[k]] }
}

-- ELL matrix-vector multiplication
pred MVM [e: ELL, x: seq Value, b: seq SumProd] {
  e.rows = #b
  e.cols = #x
  all i: range[e.rows] |
    b[i].vals = { j: Int, p, q: Value-Zero |
      some k: range[e.cols] |
        j = e.jcoef[i][k] and p = e.A[i][k] and q = x[e.jcoef[i][k]] } 
}

/*
 * Below we perform two checks:
 * 
 *   1. alphaValid checks that the abstraction function maps
 *      valid CSR representations to valid dense representations
 *
 *   2. mvmRefines checks that the CSR MVM method is a
 *      valid refinement of the dense MVM method
 */  

assert alphaValid {
  all c: CSR, m: Matrix |
    I[c] and alpha[c, m] => I[m]
}

assert mvmRefines {
  all m: Matrix, c: CSR, x: seq Value, b: seq SumProd |
    I[c] and alpha[c, m] and MVM[c, x, b]
      => MVM[m, x, b]
}

assert alphaELLValid {
  all e: ELL, m: Matrix |
    I[e] and alpha[e, m] => I[m]
}

assert mvmELLRefines {
  all m: Matrix, e: ELL, x: seq Value, b: seq SumProd |
    I[e] and alpha[e, m] and MVM[e, x, b]
      => MVM[m, x, b]
}

check alphaValid for 1 Matrix, 0 COO, 1 CSR, 0 ELL, 3 Value, 0 SumProd
check mvmRefines for 1 Matrix, 0 COO, 1 CSR, 0 ELL, 3 Value, 6 SumProd, 6 seq
