package bls12381

import (
	"errors"
	"hash"
	"math"
	"math/big"
)

// PointG1 is type for point in G1.
// PointG1 is both used for Affine and Jacobian point representation.
// If z is equal to one the point is accounted as in affine form.
type PointG1 [3]fe

func (p *PointG1) Set(p2 *PointG1) *PointG1 {
	p[0].set(&p2[0])
	p[1].set(&p2[1])
	p[2].set(&p2[2])
	return p
}

func (p *PointG1) Zero() *PointG1 {
	p[0].zero()
	p[1].one()
	p[2].zero()
	return p
}

// IsAffine checks a G1 point whether it is in affine form.
func (p *PointG1) IsAffine() bool {
	return p[2].isOne()
}

type tempG1 struct {
	t [9]*fe
}

// G1 is struct for G1 group.
type G1 struct {
	tempG1
}

// NewG1 constructs a new G1 instance.
func NewG1() *G1 {
	t := newTempG1()
	return &G1{t}
}

func newTempG1() tempG1 {
	t := [9]*fe{}
	for i := 0; i < 9; i++ {
		t[i] = &fe{}
	}
	return tempG1{t}
}

// Q returns group order in big.Int.
func (g *G1) Q() *big.Int {
	return new(big.Int).Set(qBig)
}

// FromUncompressed expects byte slice at least 96 bytes and given bytes returns a new point in G1.
// Serialization rules are in line with zcash library. See below for details.
// https://github.com/zcash/librustzcash/blob/master/pairing/src/bls12_381/README.md#serialization
// https://docs.rs/bls12_381/0.1.1/bls12_381/notes/serialization/index.html
func (g *G1) FromUncompressed(uncompressed []byte) (*PointG1, error) {
	if len(uncompressed) != 2*fpByteSize {
		return nil, errors.New("input string should be equal or larger than 96")
	}
	var in [2 * fpByteSize]byte
	copy(in[:], uncompressed[:2*fpByteSize])
	if in[0]&(1<<7) != 0 {
		return nil, errors.New("input string should be equal or larger than 96")
	}
	if in[0]&(1<<5) != 0 {
		return nil, errors.New("input string should be equal or larger than 96")
	}
	if in[0]&(1<<6) != 0 {
		for i, v := range in {
			if (i == 0 && v != 0x40) || (i != 0 && v != 0x00) {
				return nil, errors.New("input string should be equal or larger than 96")
			}
		}
		return g.Zero(), nil
	}
	in[0] &= 0x1f
	x, err := fromBytes(in[:fpByteSize])
	if err != nil {
		return nil, err
	}
	y, err := fromBytes(in[fpByteSize:])
	if err != nil {
		return nil, err
	}
	z := new(fe).one()
	p := &PointG1{*x, *y, *z}
	if !g.IsOnCurve(p) {
		return nil, errors.New("input string should be equal or larger than 96")
	}
	if !g.InCorrectSubgroup(p) {
		return nil, errors.New("input string should be equal or larger than 96")
	}
	return p, nil
}

// ToUncompressed given a G1 point returns bytes in uncompressed (x, y) form of the point.
// Serialization rules are in line with zcash library. See below for details.
// https://github.com/zcash/librustzcash/blob/master/pairing/src/bls12_381/README.md#serialization
// https://docs.rs/bls12_381/0.1.1/bls12_381/notes/serialization/index.html
func (g *G1) ToUncompressed(p *PointG1) []byte {
	out := make([]byte, 2*fpByteSize)
	if g.IsZero(p) {
		out[0] |= 1 << 6
		return out
	}
	g.Affine(p)
	copy(out[:fpByteSize], toBytes(&p[0]))
	copy(out[fpByteSize:], toBytes(&p[1]))
	return out
}

// FromCompressed expects byte slice at least 48 bytes and given bytes returns a new point in G1.
// Serialization rules are in line with zcash library. See below for details.
// https://github.com/zcash/librustzcash/blob/master/pairing/src/bls12_381/README.md#serialization
// https://docs.rs/bls12_381/0.1.1/bls12_381/notes/serialization/index.html
func (g *G1) FromCompressed(compressed []byte) (*PointG1, error) {
	if len(compressed) != fpByteSize {
		return nil, errors.New("input string should be equal or larger than 48")
	}
	var in [fpByteSize]byte
	copy(in[:], compressed[:])
	if in[0]&(1<<7) == 0 {
		return nil, errors.New("compression flag should be set")
	}
	if in[0]&(1<<6) != 0 {
		// in[0] == (1 << 6) + (1 << 7)
		for i, v := range in {
			if (i == 0 && v != 0xc0) || (i != 0 && v != 0x00) {
				return nil, errors.New("input string should be zero when infinity flag is set")
			}
		}
		return g.Zero(), nil
	}
	a := in[0]&(1<<5) != 0
	in[0] &= 0x1f
	x, err := fromBytes(in[:])
	if err != nil {
		return nil, err
	}
	// solve curve equation
	y := &fe{}
	square(y, x)
	mul(y, y, x)
	add(y, y, b)
	if ok := sqrt(y, y); !ok {
		return nil, errors.New("point is not on curve")
	}
	if y.signBE() == a {
		neg(y, y)
	}
	z := new(fe).one()
	p := &PointG1{*x, *y, *z}
	if !g.InCorrectSubgroup(p) {
		return nil, errors.New("point is not on correct subgroup")
	}
	return p, nil
}

// ToCompressed given a G1 point returns bytes in compressed form of the point.
// Serialization rules are in line with zcash library. See below for details.
// https://github.com/zcash/librustzcash/blob/master/pairing/src/bls12_381/README.md#serialization
// https://docs.rs/bls12_381/0.1.1/bls12_381/notes/serialization/index.html
func (g *G1) ToCompressed(p *PointG1) []byte {
	out := make([]byte, fpByteSize)
	g.Affine(p)
	if g.IsZero(p) {
		out[0] |= 1 << 6
	} else {
		copy(out[:], toBytes(&p[0]))
		if !p[1].signBE() {
			out[0] |= 1 << 5
		}
	}
	out[0] |= 1 << 7
	return out
}

func (g *G1) fromBytesUnchecked(in []byte) (*PointG1, error) {
	p0, err := fromBytes(in[:fpByteSize])
	if err != nil {
		return nil, err
	}
	p1, err := fromBytes(in[fpByteSize:])
	if err != nil {
		return nil, err
	}
	p2 := new(fe).one()
	return &PointG1{*p0, *p1, *p2}, nil
}

// FromBytes constructs a new point given uncompressed byte input.
// Input string is expected to be equal to 96 bytes and concatenation of x and y cooridanates.
// (0, 0) is considered as infinity.
func (g *G1) FromBytes(in []byte) (*PointG1, error) {
	if len(in) != 2*fpByteSize {
		return nil, errors.New("input string should be equal or larger than 96")
	}
	p0, err := fromBytes(in[:fpByteSize])
	if err != nil {
		return nil, err
	}
	p1, err := fromBytes(in[fpByteSize:])
	if err != nil {
		return nil, err
	}
	// check if given input points to infinity
	if p0.isZero() && p1.isZero() {
		return g.Zero(), nil
	}
	p2 := new(fe).one()
	p := &PointG1{*p0, *p1, *p2}
	if !g.IsOnCurve(p) {
		return nil, errors.New("point is not on curve")
	}
	return p, nil
}

// ToBytes serializes a point into bytes in uncompressed form.
// ToBytes returns (0, 0) if point is infinity.
func (g *G1) ToBytes(p *PointG1) []byte {
	out := make([]byte, 2*fpByteSize)
	if g.IsZero(p) {
		return out
	}
	g.Affine(p)
	copy(out[:fpByteSize], toBytes(&p[0]))
	copy(out[fpByteSize:], toBytes(&p[1]))
	return out
}

// New creates a new G1 Point which is equal to zero in other words point at infinity.
func (g *G1) New() *PointG1 {
	return g.Zero()
}

// Zero returns a new G1 Point which is equal to point at infinity.
func (g *G1) Zero() *PointG1 {
	return new(PointG1).Zero()
}

// One returns a new G1 Point which is equal to generator point.
func (g *G1) One() *PointG1 {
	p := &PointG1{}
	return p.Set(&g1One)
}

// IsZero returns true if given point is equal to zero.
func (g *G1) IsZero(p *PointG1) bool {
	return p[2].isZero()
}

// Equal checks if given two G1 point is equal in their affine form.
func (g *G1) Equal(p1, p2 *PointG1) bool {
	if g.IsZero(p1) {
		return g.IsZero(p2)
	}
	if g.IsZero(p2) {
		return g.IsZero(p1)
	}
	t := g.t
	square(t[0], &p1[2])
	square(t[1], &p2[2])
	mul(t[2], t[0], &p2[0])
	mul(t[3], t[1], &p1[0])
	mul(t[0], t[0], &p1[2])
	mul(t[1], t[1], &p2[2])
	mul(t[1], t[1], &p1[1])
	mul(t[0], t[0], &p2[1])
	return t[0].equal(t[1]) && t[2].equal(t[3])
}

// InCorrectSubgroup checks whether given point is in correct subgroup.
func (g *G1) InCorrectSubgroup(p *PointG1) bool {
	tmp := &PointG1{}
	g.MulScalar(tmp, p, q)
	return g.IsZero(tmp)
}

// IsOnCurve checks a G1 point is on curve.
func (g *G1) IsOnCurve(p *PointG1) bool {
	if g.IsZero(p) {
		return true
	}
	t := g.t
	square(t[0], &p[1])    // y^2
	square(t[1], &p[0])    // x^2
	mul(t[1], t[1], &p[0]) // x^3
	if p.IsAffine() {
		addAssign(t[1], b)      // x^2 + b
		return t[0].equal(t[1]) // y^2 ?= x^3 + b
	}
	square(t[2], &p[2])     // z^2
	square(t[3], t[2])      // z^4
	mul(t[2], t[2], t[3])   // z^6
	mul(t[2], b, t[2])      // b * z^6
	add(t[1], t[1], t[2])   // x^3 + b * z^6
	return t[0].equal(t[1]) // y^2 ?= x^3 + b * z^6
}

// IsAffine checks a G1 point whether it is in affine form.
func (g *G1) IsAffine(p *PointG1) bool {
	return p[2].isOne()
}

// Affine returns the affine representation of the given point
func (g *G1) Affine(p *PointG1) *PointG1 {
	if g.IsZero(p) {
		return p
	}
	if !g.IsAffine(p) {
		t := g.t
		inverse(t[0], &p[2])    // z^-1
		square(t[1], t[0])      // z^-2
		mul(&p[0], &p[0], t[1]) // x = x * z^-2
		mul(t[0], t[0], t[1])   // z^-3
		mul(&p[1], &p[1], t[0]) // y = y * z^-3
		p[2].one()              // z = 1
	}
	return p
}

// Affine returns the affine representation of the given point
func (g *G1) AffineBatch(p []*PointG1) {
	inverses := make([]fe, len(p))
	for i := 0; i < len(p); i++ {
		inverses[i].set(&p[i][2])
	}
	inverseBatch(inverses)
	t := g.t
	for i := 0; i < len(p); i++ {
		if !g.IsAffine(p[i]) && !g.IsZero(p[i]) {
			square(t[1], &inverses[i])
			mul(&p[i][0], &p[i][0], t[1])
			mul(t[0], &inverses[i], t[1])
			mul(&p[i][1], &p[i][1], t[0])
			p[i][2].one()
		}
	}
}

// Add adds two G1 points p1, p2 and assigns the result to point at first argument.
func (g *G1) Add(r, p1, p2 *PointG1) *PointG1 {
	// http://www.hyperelliptic.org/EFD/gp/auto-shortw-jacobian-0.html#addition-add-2007-bl
	if g.IsZero(p1) {
		return r.Set(p2)
	}
	if g.IsZero(p2) {
		return r.Set(p1)
	}
	t := g.t
	square(t[7], &p1[2])    // z1z1
	mul(t[1], &p2[0], t[7]) // u2 = x2 * z1z1
	mul(t[2], &p1[2], t[7]) // z1z1 * z1
	mul(t[0], &p2[1], t[2]) // s2 = y2 * z1z1 * z1
	square(t[8], &p2[2])    // z2z2
	mul(t[3], &p1[0], t[8]) // u1 = x1 * z2z2
	mul(t[4], &p2[2], t[8]) // z2z2 * z2
	mul(t[2], &p1[1], t[4]) // s1 = y1 * z2z2 * z2
	if t[1].equal(t[3]) {
		if t[0].equal(t[2]) {
			return g.Double(r, p1)
		} else {
			return r.Zero()
		}
	}
	subAssign(t[1], t[3])     // h = u2 - u1
	double(t[4], t[1])        // 2h
	square(t[4], t[4])        // i = 2h^2
	mul(t[5], t[1], t[4])     // j = h*i
	subAssign(t[0], t[2])     // s2 - s1
	doubleAssign(t[0])        // r = 2*(s2 - s1)
	square(t[6], t[0])        // r^2
	subAssign(t[6], t[5])     // r^2 - j
	mul(t[3], t[3], t[4])     // v = u1 * i
	double(t[4], t[3])        // 2*v
	sub(&r[0], t[6], t[4])    // x3 = r^2 - j - 2*v
	sub(t[4], t[3], &r[0])    // v - x3
	mul(t[6], t[2], t[5])     // s1 * j
	doubleAssign(t[6])        // 2 * s1 * j
	mul(t[0], t[0], t[4])     // r * (v - x3)
	sub(&r[1], t[0], t[6])    // y3 = r * (v - x3) - (2 * s1 * j)
	add(t[0], &p1[2], &p2[2]) // z1 + z2
	square(t[0], t[0])        // (z1 + z2)^2
	subAssign(t[0], t[7])     // (z1 + z2)^2 - z1z1
	subAssign(t[0], t[8])     // (z1 + z2)^2 - z1z1 - z2z2
	mul(&r[2], t[0], t[1])    // z3 = ((z1 + z2)^2 - z1z1 - z2z2) * h
	return r
}

// Add adds two G1 points p1, p2 and assigns the result to point at first argument.
// Expects point p2 in affine form.
func (g *G1) AddMixed(r, p1, p2 *PointG1) *PointG1 {
	// http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl
	if g.IsZero(p1) {
		return r.Set(p2)
	}
	if g.IsZero(p2) {
		return r.Set(p1)
	}
	t := g.t
	square(t[7], &p1[2])    // z1z1
	mul(t[1], &p2[0], t[7]) // u2 = x2 * z1z1
	mul(t[2], &p1[2], t[7]) // z1z1 * z1
	mul(t[0], &p2[1], t[2]) // s2 = y2 * z1z1 * z1

	if p1[0].equal(t[1]) && p1[1].equal(t[0]) {
		return g.Double(r, p1)
	}

	sub(t[1], t[1], &p1[0]) // h = u2 - x1
	square(t[2], t[1])      // hh
	double(t[4], t[2])
	doubleAssign(t[4])      // 4hh
	mul(t[5], t[1], t[4])   // j = h*i
	subAssign(t[0], &p1[1]) // s2 - y1
	doubleAssign(t[0])      // r = 2*(s2 - y1)
	square(t[6], t[0])      // r^2
	subAssign(t[6], t[5])   // r^2 - j
	mul(t[3], &p1[0], t[4]) // v = x1 * i
	double(t[4], t[3])      // 2*v
	sub(&r[0], t[6], t[4])  // x3 = r^2 - j - 2*v
	sub(t[4], t[3], &r[0])  // v - x3
	mul(t[6], &p1[1], t[5]) // y1 * j
	doubleAssign(t[6])      // 2 * y1 * j
	mul(t[0], t[0], t[4])   // r * (v - x3)
	sub(&r[1], t[0], t[6])  // y3 = r * (v - x3) - (2 * y1 * j)
	add(t[0], &p1[2], t[1]) // z1 + h
	square(t[0], t[0])      // (z1 + h)^2
	subAssign(t[0], t[7])   // (z1 + h)^2 - z1z1
	sub(&r[2], t[0], t[2])  // z3 = (z1 + z2)^2 - z1z1 - hh
	return r
}

// Double doubles a G1 point p and assigns the result to the point at first argument.
func (g *G1) Double(r, p *PointG1) *PointG1 {
	// http://www.hyperelliptic.org/EFD/gp/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
	if g.IsZero(p) {
		return r.Set(p)
	}
	t := g.t
	square(t[0], &p[0])     // a = x^2
	square(t[1], &p[1])     // b = y^2
	square(t[2], t[1])      // c = b^2
	add(t[1], &p[0], t[1])  // b + x1
	square(t[1], t[1])      // (b + x1)^2
	subAssign(t[1], t[0])   // (b + x1)^2 - a
	subAssign(t[1], t[2])   // (b + x1)^2 - a - c
	doubleAssign(t[1])      // d = 2((b+x1)^2 - a - c)
	double(t[3], t[0])      // 2a
	addAssign(t[0], t[3])   // e = 3a
	square(t[4], t[0])      // f = e^2
	double(t[3], t[1])      // 2d
	sub(&r[0], t[4], t[3])  // x3 = f - 2d
	subAssign(t[1], &r[0])  // d-x3
	doubleAssign(t[2])      //
	doubleAssign(t[2])      //
	doubleAssign(t[2])      // 8c
	mul(t[0], t[0], t[1])   // e * (d - x3)
	sub(t[1], t[0], t[2])   // x3 = e * (d - x3) - 8c
	mul(t[0], &p[1], &p[2]) // y1 * z1
	r[1].set(t[1])          //
	double(&r[2], t[0])     // z3 = 2(y1 * z1)
	return r
}

// Neg negates a G1 point p and assigns the result to the point at first argument.
func (g *G1) Neg(r, p *PointG1) *PointG1 {
	r[0].set(&p[0])
	r[2].set(&p[2])
	neg(&r[1], &p[1])
	return r
}

// Sub subtracts two G1 points p1, p2 and assigns the result to point at first argument.
func (g *G1) Sub(c, a, b *PointG1) *PointG1 {
	d := &PointG1{}
	g.Neg(d, b)
	g.Add(c, a, d)
	return c
}

// MulScalar multiplies a point by given scalar value in big.Int and assigns the result to point at first argument.
func (g *G1) MulScalarBig(c, p *PointG1, e *big.Int) *PointG1 {
	q, n := &PointG1{}, &PointG1{}
	n.Set(p)
	l := e.BitLen()
	for i := 0; i < l; i++ {
		if e.Bit(i) == 1 {
			g.Add(q, q, n)
		}
		g.Double(n, n)
	}
	return c.Set(q)
}

// MulScalar multiplies a point by given scalar value and assigns the result to point at first argument.
func (g *G1) MulScalar(c, p *PointG1, e *Fr) *PointG1 {
	q, n := &PointG1{}, &PointG1{}
	n.Set(p)
	for i := 0; i < frBitSize; i++ {
		if e.Bit(i) {
			g.Add(q, q, n)
		}
		g.Double(n, n)
	}
	return c.Set(q)
}

// ClearCofactor maps given a G1 point to correct subgroup
func (g *G1) ClearCofactor(p *PointG1) {
	g.MulScalarBig(p, p, cofactorEFFG1)
}

// MultiExpBig calculates multi exponentiation. Scalar values are received as big.Int type.
// Given pairs of G1 point and scalar values `(P_0, e_0), (P_1, e_1), ... (P_n, e_n)`,
// calculates `r = e_0 * P_0 + e_1 * P_1 + ... + e_n * P_n`.
// Length of points and scalars are expected to be equal, otherwise an error is returned.
// Result is assigned to point at first argument.
func (g *G1) MultiExpBig(r *PointG1, points []*PointG1, scalars []*big.Int) (*PointG1, error) {
	if len(points) != len(scalars) {
		return nil, errors.New("point and scalar vectors should be in same length")
	}

	c := 3
	if len(scalars) >= 32 {
		c = int(math.Ceil(math.Log(float64(len(scalars)))))
	}

	bucketSize := (1 << c) - 1
	windows := make([]PointG1, 255/c+1)
	bucket := make([]PointG1, bucketSize)

	for j := 0; j < len(windows); j++ {

		for i := 0; i < bucketSize; i++ {
			bucket[i].Zero()
		}

		for i := 0; i < len(scalars); i++ {
			index := bucketSize & int(new(big.Int).Rsh(scalars[i], uint(c*j)).Int64())
			if index != 0 {
				g.Add(&bucket[index-1], &bucket[index-1], points[i])
			}
		}

		acc, sum := g.New(), g.New()
		for i := bucketSize - 1; i >= 0; i-- {
			g.Add(sum, sum, &bucket[i])
			g.Add(acc, acc, sum)
		}
		windows[j].Set(acc)
	}

	acc := g.New()
	for i := len(windows) - 1; i >= 0; i-- {
		for j := 0; j < c; j++ {
			g.Double(acc, acc)
		}
		g.Add(acc, acc, &windows[i])
	}
	return r.Set(acc), nil
}

// MultiExp calculates multi exponentiation. Given pairs of G1 point and scalar values `(P_0, e_0), (P_1, e_1), ... (P_n, e_n)`,
// calculates `r = e_0 * P_0 + e_1 * P_1 + ... + e_n * P_n`. Length of points and scalars are expected to be equal,
// otherwise an error is returned. Result is assigned to point at first argument.
func (g *G1) MultiExp(r *PointG1, points []*PointG1, scalars []*Fr) (*PointG1, error) {
	if len(points) != len(scalars) {
		return nil, errors.New("point and scalar vectors should be in same length")
	}

	g.AffineBatch(points)

	c := 3
	if len(scalars) >= 32 {
		c = int(math.Ceil(math.Log(float64(len(scalars)))))
	}

	bucketSize := (1 << c) - 1
	windows := make([]*PointG1, 255/c+1)
	bucket := make([]PointG1, bucketSize)

	for j := 0; j < len(windows); j++ {

		for i := 0; i < bucketSize; i++ {
			bucket[i].Zero()
		}

		for i := 0; i < len(scalars); i++ {
			index := bucketSize & int(scalars[i].sliceUint64(c*j))
			if index != 0 {
				g.AddMixed(&bucket[index-1], &bucket[index-1], points[i])
			}
		}

		acc, sum := g.New(), g.New()
		for i := bucketSize - 1; i >= 0; i-- {
			g.Add(sum, sum, &bucket[i])
			g.Add(acc, acc, sum)
		}
		windows[j] = g.New().Set(acc)
	}

	g.AffineBatch(windows)

	acc := g.New()
	for i := len(windows) - 1; i >= 0; i-- {
		for j := 0; j < c; j++ {
			g.Double(acc, acc)
		}
		g.AddMixed(acc, acc, windows[i])
	}
	return r.Set(acc), nil
}

// MapToCurve given a byte slice returns a valid G1 point.
// This mapping function implements the Simplified Shallue-van de Woestijne-Ulas method.
// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06
// Input byte slice should be a valid field element, otherwise an error is returned.
func (g *G1) MapToCurve(in []byte) (*PointG1, error) {
	u, err := fromBytes(in)
	if err != nil {
		return nil, err
	}
	x, y := swuMapG1(u)
	isogenyMapG1(x, y)
	one := new(fe).one()
	p := &PointG1{*x, *y, *one}
	g.ClearCofactor(p)
	return g.Affine(p), nil
}

// EncodeToCurve given a message and domain seperator tag returns the hash result
// which is a valid curve point.
// Implementation follows BLS12381G1_XMD:SHA-256_SSWU_NU_ suite at
// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06
func (g *G1) EncodeToCurve(f func() hash.Hash, msg, domain []byte) (*PointG1, error) {
	hashRes, err := hashToFpXMD(f, msg, domain, 1)
	if err != nil {
		return nil, err
	}
	u := hashRes[0]
	x, y := swuMapG1(u)
	isogenyMapG1(x, y)
	one := new(fe).one()
	p := &PointG1{*x, *y, *one}
	g.ClearCofactor(p)
	return g.Affine(p), nil
}

// HashToCurve given a message and domain seperator tag returns the hash result
// which is a valid curve point.
// Implementation follows BLS12381G1_XMD:SHA-256_SSWU_RO_ suite at
// https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-06
func (g *G1) HashToCurve(f func() hash.Hash, msg, domain []byte) (*PointG1, error) {
	hashRes, err := hashToFpXMD(f, msg, domain, 2)
	if err != nil {
		return nil, err
	}
	u0, u1 := hashRes[0], hashRes[1]

	p0, p1 := osswuMap(u0), osswuMap(u1)
	g.Add(p0, p0, p1)
	g.Affine(p0)
	isogenyMapG1(&p0[0], &p0[1])
	g.ClearCofactor(p0)
	return g.Affine(p0), nil
}

var SQRT_M_XI_CUBED = &fe{
	0x43b571cad3215f1f,
	0xccb460ef1c702dc2,
	0x742d884f4f97100b,
	0xdb2c3e3238a3382b,
	0xe40f3fa13fce8f88,
	0x73a2af9892a2ff,
}

// Algorithm is re-written from Rust code (https://github.com/algorand/pairing-plus/blob/7ec2ae03aae4ba2fc5210810211478171ccededf/src/bls12_381/osswu_map/g1.rs#L48).
func osswuMap(u *fe) *PointG1 {
	var params = swuParamsForG1

	usq := new(fe)
	square(usq, u)

	xi_usq := new(fe)
	mul(xi_usq, usq, params.z) // XI

	xi2_u4 := new(fe)
	square(xi2_u4, xi_usq)

	nd_common := new(fe)
	add(nd_common, xi_usq, xi2_u4)

	x0_num := new(fe)
	add(x0_num, nd_common, new(fe).one())
	mul(x0_num, x0_num, params.b) // ELLP_B

	x0_den := new(fe)
	if nd_common.isZero() {
		mul(x0_den, params.a, params.z) // ELLP_A, XI
	} else {
		mul(x0_den, params.a, nd_common) // ELLP_A
		neg(x0_den, x0_den)
	}

	gx0_den_sq := new(fe)
	square(gx0_den_sq, x0_den)
	gx0_den := new(fe)
	mul(gx0_den, gx0_den_sq, x0_den)

	gx0_num := new(fe)
	mul(gx0_num, gx0_den, params.b) // ELLP_B
	tmp2 := new(fe)
	mul(tmp2, gx0_den_sq, x0_num)
	mul(tmp2, tmp2, params.a) // ELLP_A

	add(gx0_num, gx0_num, tmp2)

	square(tmp2, x0_num)
	mul(tmp2, tmp2, x0_num)

	add(gx0_num, gx0_num, tmp2)

	sqrt_candidate := func() *fe {
		tmp1 := new(fe)
		mul(tmp1, gx0_num, gx0_den)

		tmp2 := new(fe)
		square(tmp2, gx0_den)
		mul(tmp2, tmp2, tmp1)

		tmp3 := new(fe)
		*tmp3 = *tmp2

		chain_pm3div4(tmp2, tmp3)

		mul(tmp2, tmp2, tmp1)

		return tmp2
	}()

	test_cand := new(fe)
	square(test_cand, sqrt_candidate)
	mul(test_cand, test_cand, gx0_den)

	x_num, y := new(fe), new(fe)
	if test_cand.equal(gx0_num) {
		x_num = x0_num
		y = sqrt_candidate
	} else {
		mul(x_num, x0_num, xi_usq)

		mul(y, usq, u)
		mul(y, y, sqrt_candidate)
		mul(y, y, SQRT_M_XI_CUBED)
	}

	if y.signBE() != u.signBE() {
		neg(y, y)
	}

	mul(x_num, x_num, x0_den)
	mul(y, y, gx0_den)

	return &PointG1{
		*x_num,
		*y,
		*x0_den,
	}
}

// Algorithm is re-written from Rust code (https://github.com/algorand/pairing-plus/blob/master/src/bls12_381/osswu_map/chain.rs#L14).
func chain_pm3div4(tmpvar1, tmpvar0 *fe) {
	square(tmpvar1, tmpvar0)

	tmpvar9 := new(fe)
	mul(tmpvar9, tmpvar1, tmpvar0)

	tmpvar5 := new(fe)
	square(tmpvar5, tmpvar1)

	tmpvar2 := new(fe)
	mul(tmpvar2, tmpvar9, tmpvar1)

	tmpvar7 := new(fe)
	mul(tmpvar7, tmpvar5, tmpvar9)

	tmpvar10 := new(fe)
	mul(tmpvar10, tmpvar2, tmpvar5)

	tmpvar13 := new(fe)
	mul(tmpvar13, tmpvar7, tmpvar5)

	tmpvar4 := new(fe)
	mul(tmpvar4, tmpvar10, tmpvar5)

	tmpvar8 := new(fe)
	mul(tmpvar8, tmpvar13, tmpvar5)

	tmpvar15 := new(fe)
	mul(tmpvar15, tmpvar4, tmpvar5)

	tmpvar11 := new(fe)
	mul(tmpvar11, tmpvar8, tmpvar5)

	tmpvar3 := new(fe)
	mul(tmpvar3, tmpvar15, tmpvar5)

	tmpvar12 := new(fe)
	mul(tmpvar12, tmpvar11, tmpvar5)

	tmpvar14 := new(fe)
	mul(tmpvar14, tmpvar12, tmpvar5)

	square(tmpvar1, tmpvar4)

	tmpvar6 := new(fe)
	mul(tmpvar6, tmpvar1, tmpvar9)

	mul(tmpvar5, tmpvar1, tmpvar2)

	for i := 0; i < 12; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar15)

	for i := 0; i < 7; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar8)

	for i := 0; i < 4; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar2)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar7)

	for i := 0; i < 7; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar12)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 2; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar9)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar4)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar4)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar10)

	for i := 0; i < 3; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar9)

	for i := 0; i < 7; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar4)

	for i := 0; i < 4; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar4)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar8)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar14)

	for i := 0; i < 3; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar0)

	for i := 0; i < 8; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar4)

	for i := 0; i < 7; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar12)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar13)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar4)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar6)

	for i := 0; i < 4; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar10)

	for i := 0; i < 8; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar6)

	for i := 0; i < 4; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar4)

	for i := 0; i < 7; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar12)

	for i := 0; i < 9; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar11)

	for i := 0; i < 2; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar9)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar7)

	for i := 0; i < 7; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar2)

	for i := 0; i < 7; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar10)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar12)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar6)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar11)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar11)

	for i := 0; i < 8; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar4)

	for i := 0; i < 7; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar3)

	for i := 0; i < 9; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar8)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar4)

	for i := 0; i < 3; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar9)

	for i := 0; i < 8; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar8)

	for i := 0; i < 3; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar9)

	for i := 0; i < 7; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar10)

	for i := 0; i < 9; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar8)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar3)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 4; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar4)

	for i := 0; i < 3; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar9)

	for i := 0; i < 8; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar3)

	for i := 0; i < 7; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 4; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar8)

	for i := 0; i < 4; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar7)

	for i := 0; i < 7; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar6)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 5; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar5)

	for i := 0; i < 4; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar4)

	for i := 0; i < 6; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar3)

	for i := 0; i < 4; i++ {
		square(tmpvar1, tmpvar1)
	}
	mul(tmpvar1, tmpvar1, tmpvar2)

	square(tmpvar1, tmpvar1)
}
