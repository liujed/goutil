package sets

import (
	"encoding/json"
	"fmt"
	"slices"
	"strings"
	"testing"

	"github.com/liujed/goutil/optionals"
	"github.com/stretchr/testify/assert"
)

func TestAdd(t *testing.T) {
	ops := []struct {
		toAdd         string
		expectedCount int
	}{
		{"foo", 1},
		{"foo", 1},
		{"bar", 2},
		{"foo", 2},
		{"bar", 2},
		{"baz", 3},
		{"foo", 3},
		{"bar", 3},
		{"baz", 3},
	}
	s := NewHashSet[string]()
	for _, op := range ops {
		s.Add(op.toAdd)
		assert.Equal(t, op.expectedCount, s.Size())
		assert.True(t, s.Contains(op.toAdd))
	}
}

func TestClear(t *testing.T) {
	type TestCase struct {
		InitialElts []string
	}
	testCases := map[string]TestCase{
		"empty set": {
			InitialElts: nil,
		},
		"non-empty set": {
			InitialElts: []string{"foo", "bar", "baz"},
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.InitialElts...)
		s.Clear()

		// Should end up with an empty set.
		assert.Equal(t, NewHashSet[string](), s, name)
	}
}

func TestChoose(t *testing.T) {
	type TestCase struct {
		SetElts []string
	}
	testCases := map[string]TestCase{
		"empty set": {
			SetElts: nil,
		},
		"non-empty set": {
			SetElts: []string{"foo", "bar", "baz"},
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		actual := s.Choose()

		// Expect that the set is unchanged.
		expectedS := NewHashSet(tc.SetElts...)
		assert.Equal(t, expectedS, s, name)

		if len(tc.SetElts) == 0 {
			// Expect None.
			assert.True(t, actual.IsNone(), name)
		} else {
			// Expect a member of the set.
			elt, exists := actual.Get()
			assert.True(t, exists, name)
			assert.True(t, expectedS.Contains(elt), name)
		}
	}
}

func TestContains(t *testing.T) {
	type TestCase struct {
		SetElts []string
		NonElt  string
	}
	testCases := map[string]TestCase{
		"empty set": {
			SetElts: nil,
			NonElt:  "foo",
		},
		"non-empty set": {
			SetElts: []string{"foo", "bar", "baz"},
			NonElt:  "qux",
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		for _, elt := range tc.SetElts {
			assert.True(t, s.Contains(elt), name)
		}
		assert.False(t, s.Contains(tc.NonElt), name)
	}
}

func TestCount(t *testing.T) {
	type TestCase struct {
		SetElts       []string
		MakeCountFun  func() func(string) (bool, error)
		ExpectedCount int
		ExpectError   bool
	}
	testCases := map[string]TestCase{
		"empty set, true, no error": {
			SetElts: nil,
			MakeCountFun: func() func(string) (bool, error) {
				return func(string) (bool, error) {
					return true, nil
				}
			},
			ExpectedCount: 0,
			ExpectError:   false,
		},
		"empty set, false, no error": {
			SetElts: nil,
			MakeCountFun: func() func(string) (bool, error) {
				return func(string) (bool, error) {
					return false, nil
				}
			},
			ExpectedCount: 0,
			ExpectError:   false,
		},
		"empty set, true, error": {
			SetElts: nil,
			MakeCountFun: func() func(string) (bool, error) {
				return func(string) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			ExpectedCount: 0,
			// Empty set, so count function doesn't get called, so no error expected.
			ExpectError: false,
		},
		"empty set, false, error": {
			SetElts: nil,
			MakeCountFun: func() func(string) (bool, error) {
				return func(string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedCount: 0,
			// Empty set, so count function doesn't get called, so no error expected.
			ExpectError: false,
		},
		"non-empty set, true, no error": {
			SetElts: []string{"foo", "bar", "baz", "qux"},
			MakeCountFun: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, nil
				}
			},
			ExpectedCount: 4,
			ExpectError:   false,
		},
		"non-empty set, false, no error": {
			SetElts: []string{"foo", "bar", "baz", "qux"},
			MakeCountFun: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, nil
				}
			},
			ExpectedCount: 0,
			ExpectError:   false,
		},
		"non-empty set, starts with b, no error": {
			SetElts: []string{"foo", "bar", "baz", "qux"},
			MakeCountFun: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return strings.HasPrefix(s, "b"), nil
				}
			},
			ExpectedCount: 2,
			ExpectError:   false,
		},
		"non-empty set, starts with z, no error": {
			SetElts: []string{"foo", "bar", "baz", "qux"},
			MakeCountFun: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return strings.HasPrefix(s, "z"), nil
				}
			},
			ExpectedCount: 0,
			ExpectError:   false,
		},
		"non-empty set, true, error": {
			SetElts: []string{"foo", "bar", "baz", "qux"},
			MakeCountFun: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			ExpectedCount: 1,
			ExpectError:   true,
		},
		"non-empty set, false, error": {
			SetElts: []string{"foo", "bar", "baz", "qux"},
			MakeCountFun: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedCount: 0,
			ExpectError:   true,
		},
		"non-empty set, true, error on second element": {
			SetElts: []string{"foo", "bar", "baz", "qux"},
			MakeCountFun: func() func(string) (bool, error) {
				i := 0
				return func(s string) (bool, error) {
					i++
					if i == 2 {
						return true, fmt.Errorf("")
					}
					return true, nil
				}
			},
			ExpectedCount: 2,
			ExpectError:   true,
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		count, err := s.Count(tc.MakeCountFun())

		// Expect that the set is unchanged.
		assert.Equal(t, NewHashSet(tc.SetElts...), s, name)

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}
		assert.Equal(t, tc.ExpectedCount, count, name)
	}
}

func TestCountNoError(t *testing.T) {
	type TestCase struct {
		SetElts       []string
		MakeCountFun  func() func(string) bool
		ExpectedCount int
	}
	testCases := map[string]TestCase{
		"empty set, true": {
			SetElts: nil,
			MakeCountFun: func() func(string) bool {
				return func(s string) bool {
					return true
				}
			},
			ExpectedCount: 0,
		},
		"empty set, false": {
			SetElts: nil,
			MakeCountFun: func() func(string) bool {
				return func(s string) bool {
					return false
				}
			},
			ExpectedCount: 0,
		},
		"non-empty set, true": {
			SetElts: []string{"foo", "bar", "baz", "qux"},
			MakeCountFun: func() func(string) bool {
				return func(s string) bool {
					return true
				}
			},
			ExpectedCount: 4,
		},
		"non-empty set, false": {
			SetElts: []string{"foo", "bar", "baz", "qux"},
			MakeCountFun: func() func(string) bool {
				return func(s string) bool {
					return false
				}
			},
			ExpectedCount: 0,
		},
		"non-empty set, starts with b": {
			SetElts: []string{"foo", "bar", "baz", "qux"},
			MakeCountFun: func() func(string) bool {
				return func(s string) bool {
					return strings.HasPrefix(s, "b")
				}
			},
			ExpectedCount: 2,
		},
		"non-empty set, starts with z": {
			SetElts: []string{"foo", "bar", "baz", "qux"},
			MakeCountFun: func() func(string) bool {
				return func(s string) bool {
					return strings.HasPrefix(s, "z")
				}
			},
			ExpectedCount: 0,
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		count := s.CountNoError(tc.MakeCountFun())

		// Expect that the set is unchanged.
		assert.Equal(t, NewHashSet(tc.SetElts...), s, name)

		assert.Equal(t, tc.ExpectedCount, count, name)
	}
}

func TestElements(t *testing.T) {
	s := NewHashSet[string]()
	for range s.Elements() {
		t.Error("shouldn't reach here")
	}

	s = NewHashSet("foo", "bar", "baz")
	remaining := NewHashSet("foo", "bar", "baz")
	for elt := range s.Elements() {
		assert.True(t, remaining.Contains(elt))
		remaining.Remove(elt)
	}
	assert.True(t, remaining.IsEmpty())
}

func TestExists(t *testing.T) {
	type TestCase struct {
		SetElts        []string
		MakePredicate  func() func(string) (bool, error)
		ExpectedExists bool
		ExpectError    bool
	}
	testCases := map[string]TestCase{
		"empty set, true, no error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, nil
				}
			},
			ExpectedExists: false,
			ExpectError:    false,
		},
		"empty set, false, no error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, nil
				}
			},
			ExpectedExists: false,
			ExpectError:    false,
		},
		"empty set, true, error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			ExpectedExists: false,
			// Empty set, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"empty set, false, error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedExists: false,
			// Empty set, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"non-empty set, true, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, nil
				}
			},
			ExpectedExists: true,
			ExpectError:    false,
		},
		"non-empty set, false, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, nil
				}
			},
			ExpectedExists: false,
			ExpectError:    false,
		},
		"non-empty set, starts with f, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return strings.HasPrefix(s, "f"), nil
				}
			},
			ExpectedExists: true,
			ExpectError:    false,
		},
		"non-empty set, starts with z, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return strings.HasPrefix(s, "z"), nil
				}
			},
			ExpectedExists: false,
			ExpectError:    false,
		},
		"non-empty set, true, error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			ExpectedExists: true,
			ExpectError:    true,
		},
		"non-empty set, false, error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedExists: false,
			ExpectError:    true,
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		exists, err := s.Exists(tc.MakePredicate())

		// Expect that the set is unchanged.
		assert.Equal(t, NewHashSet(tc.SetElts...), s, name)

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}
		assert.Equal(t, tc.ExpectedExists, exists, name)
	}
}

func TestExistsNoError(t *testing.T) {
	type TestCase struct {
		SetElts        []string
		MakePredicate  func() func(string) bool
		ExpectedExists bool
	}
	testCases := map[string]TestCase{
		"empty set, true": {
			SetElts: nil,
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return true
				}
			},
			ExpectedExists: false,
		},
		"empty set, false": {
			SetElts: nil,
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return false
				}
			},
			ExpectedExists: false,
		},
		"non-empty set, true, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return true
				}
			},
			ExpectedExists: true,
		},
		"non-empty set, false, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return false
				}
			},
			ExpectedExists: false,
		},
		"non-empty set, starts with f, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return strings.HasPrefix(s, "f")
				}
			},
			ExpectedExists: true,
		},
		"non-empty set, starts with z, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return strings.HasPrefix(s, "z")
				}
			},
			ExpectedExists: false,
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		exists := s.ExistsNoError(tc.MakePredicate())

		// Expect that the set is unchanged.
		assert.Equal(t, NewHashSet(tc.SetElts...), s, name)

		assert.Equal(t, tc.ExpectedExists, exists, name)
	}
}

func TestFilter(t *testing.T) {
	type TestCase struct {
		SetElts       []string
		MakePredicate func() func(string) (bool, error)
		// If given, then an assertion will be made about the resulting set's
		// elements.
		ExpectedElts optionals.Optional[[]string]
		ExpectedSize int
		ExpectError  bool
	}
	testCases := map[string]TestCase{
		"empty set, true, no error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, nil
				}
			},
			ExpectedElts: optionals.Some[[]string](nil),
			ExpectedSize: 0,
			ExpectError:  false,
		},
		"empty set, false, no error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, nil
				}
			},
			ExpectedElts: optionals.Some[[]string](nil),
			ExpectedSize: 0,
			ExpectError:  false,
		},
		"empty set, true, error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			ExpectedElts: optionals.Some[[]string](nil),
			ExpectedSize: 0,
			// Empty set, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"empty set, false, error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedElts: optionals.Some[[]string](nil),
			ExpectedSize: 0,
			// Empty set, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"non-empty set, true, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, nil
				}
			},
			ExpectedElts: optionals.Some([]string{"foo", "bar", "baz"}),
			ExpectedSize: 3,
			ExpectError:  false,
		},
		"non-empty set, false, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, nil
				}
			},
			ExpectedElts: optionals.Some[[]string](nil),
			ExpectedSize: 0,
			ExpectError:  false,
		},
		"non-empty set, starts with b, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return strings.HasPrefix(s, "b"), nil
				}
			},
			ExpectedElts: optionals.Some([]string{"bar", "baz"}),
			ExpectedSize: 2,
			ExpectError:  false,
		},
		"non-empty set, true, error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			ExpectedElts: optionals.Some([]string{"foo", "bar", "baz"}),
			ExpectedSize: 3,
			ExpectError:  true,
		},
		"non-empty set, false, error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedElts: optionals.Some([]string{"foo", "bar", "baz"}),
			ExpectedSize: 3,
			ExpectError:  true,
		},
		"non-empty set, false, error on second element": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				i := 0
				return func(s string) (bool, error) {
					i++
					if i < 2 {
						return false, nil
					}
					return false, fmt.Errorf("")
				}
			},
			// Expect first element to be removed.
			ExpectedSize: 2,
			ExpectError:  true,
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		err := s.Filter(tc.MakePredicate())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		if expectedElts, exists := tc.ExpectedElts.Get(); exists {
			assert.Equal(t, NewHashSet(expectedElts...), s, name)
		}

		assert.Equal(t, tc.ExpectedSize, s.Size(), name)
	}
}

func TestFilterNoError(t *testing.T) {
	type TestCase struct {
		SetElts       []string
		MakePredicate func() func(string) bool
		ExpectedElts  []string
	}
	testCases := map[string]TestCase{
		"empty set, true": {
			SetElts: nil,
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return true
				}
			},
			ExpectedElts: nil,
		},
		"empty set, false": {
			SetElts: nil,
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return false
				}
			},
			ExpectedElts: nil,
		},
		"non-empty set, true": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return true
				}
			},
			ExpectedElts: []string{"foo", "bar", "baz"},
		},
		"non-empty set, false": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return false
				}
			},
			ExpectedElts: nil,
		},
		"non-empty set, starts with b": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return strings.HasPrefix(s, "b")
				}
			},
			ExpectedElts: []string{"bar", "baz"},
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		s.FilterNoError(tc.MakePredicate())

		assert.Equal(t, NewHashSet(tc.ExpectedElts...), s, name)
	}
}

func TestFind(t *testing.T) {
	type TestCase struct {
		SetElts     []string
		Predicate   func(string) (bool, error)
		ExpectFind  bool
		ExpectError bool
	}
	testCases := map[string]TestCase{
		"empty set, true, no error": {
			SetElts: nil,
			Predicate: func(string) (bool, error) {
				return true, nil
			},
			ExpectFind:  false,
			ExpectError: false,
		},
		"empty set, false, no error": {
			SetElts: nil,
			Predicate: func(string) (bool, error) {
				return false, nil
			},
			ExpectFind:  false,
			ExpectError: false,
		},
		"empty set, true, error": {
			SetElts: nil,
			Predicate: func(string) (bool, error) {
				return true, fmt.Errorf("")
			},
			ExpectFind: false,
			// Empty set, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"empty set, false, error": {
			SetElts: nil,
			Predicate: func(string) (bool, error) {
				return false, fmt.Errorf("")
			},
			ExpectFind: false,
			// Empty set, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"non-empty set, true, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			Predicate: func(string) (bool, error) {
				return true, nil
			},
			ExpectFind:  true,
			ExpectError: false,
		},
		"non-empty set, false, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			Predicate: func(string) (bool, error) {
				return false, nil
			},
			ExpectFind:  false,
			ExpectError: false,
		},
		"non-empty set, starts with f, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			Predicate: func(s string) (bool, error) {
				return strings.HasPrefix(s, "f"), nil
			},
			ExpectFind:  true,
			ExpectError: false,
		},
		"non-empty set, starts with z, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			Predicate: func(s string) (bool, error) {
				return strings.HasPrefix(s, "z"), nil
			},
			ExpectFind:  false,
			ExpectError: false,
		},
		"non-empty set, true, error": {
			SetElts: []string{"foo", "bar", "baz"},
			Predicate: func(string) (bool, error) {
				return true, fmt.Errorf("")
			},
			ExpectFind:  true,
			ExpectError: true,
		},
		"non-empty set, false, error": {
			SetElts: []string{"foo", "bar", "baz"},
			Predicate: func(string) (bool, error) {
				return false, fmt.Errorf("")
			},
			ExpectFind:  false,
			ExpectError: true,
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		eltOpt, err := s.Find(tc.Predicate)

		// Expect that the set is unchanged.
		assert.Equal(t, NewHashSet(tc.SetElts...), s, name)

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		if tc.ExpectFind {
			elt, exists := eltOpt.Get()
			assert.True(t, exists, name)

			// Element must satisfy predicate.
			sat, _ := tc.Predicate(elt)
			assert.True(t, sat, name)
		} else {
			assert.True(t, eltOpt.IsNone(), name)
		}
	}
}

func TestFindNoError(t *testing.T) {
	type TestCase struct {
		SetElts    []string
		Predicate  func(string) bool
		ExpectFind bool
	}
	testCases := map[string]TestCase{
		"empty set, true": {
			SetElts: nil,
			Predicate: func(string) bool {
				return true
			},
			ExpectFind: false,
		},
		"empty set, false": {
			SetElts: nil,
			Predicate: func(string) bool {
				return false
			},
			ExpectFind: false,
		},
		"non-empty set, true": {
			SetElts: []string{"foo", "bar", "baz"},
			Predicate: func(string) bool {
				return true
			},
			ExpectFind: true,
		},
		"non-empty set, false": {
			SetElts: []string{"foo", "bar", "baz"},
			Predicate: func(string) bool {
				return false
			},
			ExpectFind: false,
		},
		"non-empty set, starts with f": {
			SetElts: []string{"foo", "bar", "baz"},
			Predicate: func(s string) bool {
				return strings.HasPrefix(s, "f")
			},
			ExpectFind: true,
		},
		"non-empty set, starts with z": {
			SetElts: []string{"foo", "bar", "baz"},
			Predicate: func(s string) bool {
				return strings.HasPrefix(s, "z")
			},
			ExpectFind: false,
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		eltOpt := s.FindNoError(tc.Predicate)

		// Expect that the set is unchanged.
		assert.Equal(t, NewHashSet(tc.SetElts...), s, name)

		if tc.ExpectFind {
			elt, exists := eltOpt.Get()
			assert.True(t, exists, name)

			// Element must satisfy predicate.
			assert.True(t, tc.Predicate(elt), name)
		} else {
			assert.True(t, eltOpt.IsNone(), name)
		}
	}
}

func TestForAll(t *testing.T) {
	type TestCase struct {
		SetElts        []string
		MakePredicate  func() func(string) (bool, error)
		ExpectedResult bool
		ExpectError    bool
	}
	testCases := map[string]TestCase{
		"empty set, true, no error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, nil
				}
			},
			// Empty set, so vacuously true.
			ExpectedResult: true,
			ExpectError:    false,
		},
		"empty set, false, no error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, nil
				}
			},
			// Empty set, so vacuously true.
			ExpectedResult: true,
			ExpectError:    false,
		},
		"empty set, true, error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			// Empty set, so vacuously true.
			ExpectedResult: true,
			// Empty set, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"empty set, false, error": {
			SetElts: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			// Empty set, so vacuously true.
			ExpectedResult: true,
			// Empty set, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"non-empty set, true, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, nil
				}
			},
			ExpectedResult: true,
			ExpectError:    false,
		},
		"non-empty set, false, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, nil
				}
			},
			ExpectedResult: false,
			ExpectError:    false,
		},
		"non-empty set, length is 3, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return len(s) == 3, nil
				}
			},
			ExpectedResult: true,
			ExpectError:    false,
		},
		"non-empty set, starts with f, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return strings.HasPrefix(s, "f"), nil
				}
			},
			ExpectedResult: false,
			ExpectError:    false,
		},
		"non-empty set, true, error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			// Predicate returns true for all elements up to and including the error.
			ExpectedResult: true,
			ExpectError:    true,
		},
		"non-empty set, false, error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedResult: false,
			ExpectError:    true,
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		all, err := s.ForAll(tc.MakePredicate())

		// Expect that the set is unchanged.
		assert.Equal(t, NewHashSet(tc.SetElts...), s, name)

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}
		assert.Equal(t, tc.ExpectedResult, all, name)
	}
}

func TestForAllNoError(t *testing.T) {
	type TestCase struct {
		SetElts        []string
		MakePredicate  func() func(string) bool
		ExpectedResult bool
	}
	testCases := map[string]TestCase{
		"empty set, true": {
			SetElts: nil,
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return true
				}
			},
			// Empty set, so vacuously true.
			ExpectedResult: true,
		},
		"empty set, false": {
			SetElts: nil,
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return false
				}
			},
			// Empty set, so vacuously true.
			ExpectedResult: true,
		},
		"non-empty set, true": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return true
				}
			},
			ExpectedResult: true,
		},
		"non-empty set, false": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return false
				}
			},
			ExpectedResult: false,
		},
		"non-empty set, length is 3": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return len(s) == 3
				}
			},
			ExpectedResult: true,
		},
		"non-empty set, starts with f": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return strings.HasPrefix(s, "f")
				}
			},
			ExpectedResult: false,
		},
	}

	for name, tc := range testCases {
		s := NewHashSet(tc.SetElts...)
		all := s.ForAllNoError(tc.MakePredicate())

		// Expect that the set is unchanged.
		assert.Equal(t, NewHashSet(tc.SetElts...), s, name)

		assert.Equal(t, tc.ExpectedResult, all, name)
	}
}

func TestIsEmpty(t *testing.T) {
	s := NewHashSet[any]()
	assert.True(t, s.IsEmpty())

	s.Add("")
	assert.False(t, s.IsEmpty())
}

func TestRemove(t *testing.T) {
	s := NewHashSet[string]()
	s.Remove("foo")
	assert.Equal(t, NewHashSet[string](), s)

	s = NewHashSet("foo", "bar", "baz")
	s.Remove("foo")
	assert.Equal(t, NewHashSet("bar", "baz"), s)
}

func TestSize(t *testing.T) {
	elts := []string{"foo", "bar", "baz"}
	s := NewHashSet[any]()
	for count, elt := range elts {
		assert.Equal(t, count, s.Size())
		s.Add(elt)
	}

	for _, elt := range elts {
		assert.Equal(t, len(elts), s.Size())
		s.Add(elt)
	}

	assert.Equal(t, len(elts), s.Size())
}

func TestToSlice(t *testing.T) {
	s := NewHashSet[string]()
	slice := s.ToSlice()
	assert.Equal(t, []string{}, slice)

	elts := []string{"foo", "bar", "baz"}
	s = NewHashSet(elts...)
	slice = s.ToSlice()
	slices.Sort(elts)
	slices.Sort(slice)
	assert.Equal(t, elts, slice)
}

func TestJSON(t *testing.T) {
	s := NewHashSet("foo", "bar", "baz")

	// Round-trip test: unmarshal(marshal(s)) == s
	jsonData, err := json.Marshal(s)
	assert.NoError(t, err)

	var deserialized HashSet[string]
	err = json.Unmarshal(jsonData, &deserialized)
	assert.NoError(t, err)
	assert.Equal(t, s, deserialized)

	// Test error handling in unmarshalling.
	err = json.Unmarshal([]byte(`"foobar"`), &deserialized)
	assert.Error(t, err)
}
