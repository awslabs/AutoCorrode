typedef struct {
  unsigned int coeffs[4];
} poly_t;

unsigned int keep_add(unsigned int x, unsigned int y) {
  return x + y;
}

unsigned int drop_mul(unsigned int x, unsigned int y) {
  return x * y;
}

unsigned int poly_get0(poly_t *p) {
  return p->coeffs[0];
}
