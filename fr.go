package bls12381

import (
	"crypto/rand"
	"errors"
	"io"
	"math/big"
	"math/bits"
)

const frByteSize = 32
const frBitSize = 255
const frNumberOfLimbs = 4

type Fr [4]uint64

func NewFr() *Fr {
	return &Fr{}
}

func (e *Fr) Rand(r io.Reader) (*Fr, error) {
	bi, err := rand.Int(r, qBig)
	if err != nil {
		return nil, err
	}
	_ = e.SetBig(bi)
	return e, nil
}

func (e *Fr) Set(e2 *Fr) *Fr {
	e[0] = e2[0]
	e[1] = e2[1]
	e[2] = e2[2]
	e[3] = e2[3]
	return e
}

func (e *Fr) Zero() *Fr {
	e[0] = 0
	e[1] = 0
	e[2] = 0
	e[3] = 0
	return e
}

func (e *Fr) One() *Fr {
	e.Set(&Fr{1})
	return e
}

func (e *Fr) RedOne() *Fr {
	e.Set(sr1)
	return e
}

func (e *Fr) FromBytes(in []byte) *Fr {
	e.setBytes(in)
	return e
}

func (e *Fr) RedFromBytes(in []byte) *Fr {
	e.setBytes(in)
	e.toMont()
	return e
}

func (e *Fr) setBytes(in []byte) {
	u := new(big.Int).SetBytes(in)
	_ = e.SetBig(u)
}

func (e *Fr) SetBig(in *big.Int) error {
	zero := new(big.Int)
	e.Zero()
	c := in.Cmp(zero)
	if c == -1 {
		return errors.New("cannot set negative element")
	} else if c == 0 {
		return nil
	}
	_in := new(big.Int)
	c = in.Cmp(qBig)
	if c == 0 {
		return nil
	} else if c == -1 {
		_in.Set(in)
	} else {
		_in = new(big.Int).Mod(in, qBig)
	}
	words := _in.Bits()
	for i := 0; i < len(words); i++ {
		e[i] = uint64(words[i])
	}
	return nil
}

func (e *Fr) ToBytes() []byte {
	return NewFr().Set(e).bytes()
}

func (e *Fr) RedToBytes() []byte {
	out := NewFr().Set(e)
	out.fromMont()
	return out.bytes()
}

func (e *Fr) ToBig() *big.Int {
	return new(big.Int).SetBytes(e.ToBytes())
}

func (e *Fr) RedToBig() *big.Int {
	return new(big.Int).SetBytes(e.RedToBytes())
}

func (e *Fr) bytes() []byte {
	out := make([]byte, frByteSize)
	var a int
	for i := 0; i < frNumberOfLimbs; i++ {
		a = frByteSize - i*8
		out[a-1] = byte(e[i])
		out[a-2] = byte(e[i] >> 8)
		out[a-3] = byte(e[i] >> 16)
		out[a-4] = byte(e[i] >> 24)
		out[a-5] = byte(e[i] >> 32)
		out[a-6] = byte(e[i] >> 40)
		out[a-7] = byte(e[i] >> 48)
		out[a-8] = byte(e[i] >> 56)
	}
	return out
}

func (e *Fr) IsZero() bool {
	return (e[3] | e[2] | e[1] | e[0]) == 0
}

func (e *Fr) IsOne() bool {
	return e.Equal(&Fr{1})
}

func (e *Fr) IsRedOne() bool {
	return e.Equal(sr1)
}

func (e *Fr) Equal(e2 *Fr) bool {
	return e2[0] == e[0] && e2[1] == e[1] && e2[2] == e[2] && e2[3] == e[3]
}

func (e *Fr) Cmp(e1 *Fr) int {
	for i := 3; i >= 0; i-- {
		if e[i] > e1[i] {
			return 1
		} else if e[i] < e1[i] {
			return -1
		}
	}
	return 0
}

func (e *Fr) sliceUint64(from int) uint64 {
	if from < 64 {
		return e[0]>>from | e[1]<<(64-from)
	} else if from < 128 {
		return e[1]>>(from-64) | e[2]<<(128-from)
	} else if from < 192 {
		return e[2]>>(from-128) | e[3]<<(192-from)
	}
	return e[3] >> (from - 192)
}

func (e *Fr) div2() {
	e[0] = e[0]>>1 | e[1]<<63
	e[1] = e[1]>>1 | e[2]<<63
	e[2] = e[2]>>1 | e[3]<<63
	e[3] = e[3] >> 1
}

func (e *Fr) mul2() uint64 {
	res := e[3] >> 63
	e[3] = e[3]<<1 | e[2]>>63
	e[2] = e[2]<<1 | e[1]>>63
	e[1] = e[1]<<1 | e[0]>>63
	e[0] = e[0] << 1

	return res
}

func (e *Fr) Bit(at int) bool {
	if at < 64 {
		return (e[0]>>at)&1 == 1
	} else if at < 128 {
		return (e[1]>>(at-64))&1 == 1
	} else if at < 192 {
		return (e[2]>>(at-128))&1 == 1
	} else if at < 256 {
		return (e[3]>>(at-192))&1 == 1
	}
	return false
}

func (e *Fr) toMont() {
	e.RedMul(e, sr2)
}

func (e *Fr) fromMont() {
	e.RedMul(e, &Fr{1})
}

func (e *Fr) Add(a, b *Fr) {
	addFR(e, a, b)
}

func (e *Fr) Double(a *Fr) {
	doubleFR(e, a)
}

func (e *Fr) Sub(a, b *Fr) {
	subFR(e, a, b)
}

func (e *Fr) Mul(a, b *Fr) {
	mulFR(e, a, b)
	mulFR(e, e, sr2)
}

func (e *Fr) RedMul(a, b *Fr) {
	mulFR(e, a, b)
}

func (e *Fr) Square(a *Fr) {
	squareFR(e, a)
	mulFR(e, e, sr2)
}

func (e *Fr) RedSquare(a *Fr) {
	squareFR(e, a)
}

func (e *Fr) Neg(a *Fr) {
	negFR(e, a)
}

func (e *Fr) Exp(a *Fr, ee *big.Int) {
	z := new(Fr).RedOne()
	for i := ee.BitLen(); i >= 0; i-- {
		z.RedSquare(z)
		if ee.Bit(i) == 1 {
			z.RedMul(z, a)
		}
	}
	e.Set(z)
}

func (e *Fr) isOdd() bool {
	var mask uint64 = 1
	return e[0]&mask != 0
}

func (e *Fr) isEven() bool {
	var mask uint64 = 1
	return e[0]&mask == 0
}

// AddNoCarry finds the value of 384-bit a + b and returns the
// resulting 384-bit value.
func (e *Fr) AddNoCarry(g *Fr) {
	carry := uint64(0)
	for i := 0; i < 4; i++ {
		e[i], carry = AddWithCarry(e[i], g[i], carry)
	}
}

// AddWithCarry finds the value a + b + carry and returns the
// full 128-bit value in 2 64-bit integers.
func AddWithCarry(a, b, carry uint64) (uint64, uint64) {
	out, outCarry := bits.Add64(a, b, 0)
	out, outCarry2 := bits.Add64(out, carry, 0)
	return out, outCarry + outCarry2
}

// SubNoBorrow subtracts two FRReprs from another and does not handle
// borrow.
func (e *Fr) SubNoBorrow(g *Fr) {
	borrow := uint64(0)
	for i := 0; i < 4; i++ {
		e[i], borrow = SubWithBorrow(e[i], g[i], borrow)
	}
}

// SubWithBorrow finds the value a - b - borrow and returns the
// result and the borrow.
func SubWithBorrow(a, b, borrow uint64) (uint64, uint64) {
	o, c := bits.Sub64(a, b, borrow)
	return o, c
}

// SubAssign subtracts a field element from this one.
func (e *Fr) SubAssign(other *Fr) {
	if other.Cmp(e) > 0 {
		e.AddNoCarry(RFieldModulus)
	}
	e.SubNoBorrow(other)
}

// RFieldModulus is the modulus of the R field.
var RFieldModulus = &Fr{
	18446744069414584321,
	6034159408538082302,
	3691218898639771653,
	8353516859464449352,
}

// Inverse finds the inverse of the field element.
func (e *Fr) Inverse() *Fr {
	if e.IsZero() {
		return nil
	}
	u := NewFr().Set(e)

	v := NewFr().Set(RFieldModulus)
	b := &Fr{ //R^2 % r.
		14526898881837571181,
		3129137299524312099,
		419701826671360399,
		524908885293268753,
	}
	c := NewFr().Zero()

	one := &Fr{1, 0, 0, 0}
	for u.Cmp(one) != 0 && v.Cmp(one) != 0 {
		for u.isEven() {
			u.div2()
			if b.isEven() {
				b.div2()
			} else {
				b.AddNoCarry(RFieldModulus)
				b.div2()
			}
		}

		for v.isEven() {
			v.div2()
			if c.isEven() {
				c.div2()
			} else {
				c.AddNoCarry(RFieldModulus)
				c.div2()
			}
		}

		if u.Cmp(v) >= 0 {
			u.SubNoBorrow(v)
			b.SubAssign(c)
		} else {
			v.SubNoBorrow(u)
			c.SubAssign(b)
		}
	}
	if u.Equal(one) {
		return b
	}
	return c
}
