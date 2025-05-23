package setfun

import (
	"fmt"
	"strings"
	"testing"

	"github.com/liujed/goutil/optionals"
	"github.com/liujed/goutil/sets"
	"github.com/stretchr/testify/assert"
)

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
			// Expect just the first element to be added to the resulting set.
			ExpectedSize: 1,
			ExpectError:  true,
		},
		"non-empty set, false, error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedElts: optionals.Some[[]string](nil),
			ExpectedSize: 0,
			ExpectError:  true,
		},
	}

	for name, tc := range testCases {
		s := sets.NewHashSet(tc.SetElts...)
		s2, err := Filter(s, tc.MakePredicate())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		// Expect that the set is unchanged.
		assert.Equal(t, sets.NewHashSet(tc.SetElts...), s, name)

		if expectedElts, exists := tc.ExpectedElts.Get(); exists {
			assert.Equal(t, sets.NewHashSet(expectedElts...), s2, name)
		}

		assert.Equal(t, tc.ExpectedSize, s2.Size(), name)
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
		s := sets.NewHashSet(tc.SetElts...)
		s2 := FilterNoError(s, tc.MakePredicate())

		// Expect that the set is unchanged.
		assert.Equal(t, sets.NewHashSet(tc.SetElts...), s, name)

		assert.Equal(t, sets.NewHashSet(tc.ExpectedElts...), s2, name)
	}
}

func TestFilterMap(t *testing.T) {
	type TestCase struct {
		SetElts       []string
		MakeFilterMap func() func(string) (optionals.Optional[int], error)
		ExpectedElts  []int
		ExpectError   bool
	}
	testCases := map[string]TestCase{
		"empty set, zero, no error": {
			SetElts: nil,
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(s string) (optionals.Optional[int], error) {
					return optionals.Some(0), nil
				}
			},
			ExpectedElts: nil,
			ExpectError:  false,
		},
		"empty set, none, no error": {
			SetElts: nil,
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(s string) (optionals.Optional[int], error) {
					return optionals.None[int](), nil
				}
			},
			ExpectedElts: nil,
			ExpectError:  false,
		},
		"empty set, zero, error": {
			SetElts: nil,
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(s string) (optionals.Optional[int], error) {
					return optionals.Some(0), fmt.Errorf("")
				}
			},
			ExpectedElts: nil,
			// Empty set, so filter/map function doesn't get called, so no error
			// expected.
			ExpectError: false,
		},
		"empty set, none, error": {
			SetElts: nil,
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(s string) (optionals.Optional[int], error) {
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedElts: nil,
			// Empty set, so filter/map function doesn't get called, so no error
			// expected.
			ExpectError: false,
		},
		"non-empty set, zero, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(s string) (optionals.Optional[int], error) {
					return optionals.Some(0), nil
				}
			},
			ExpectedElts: []int{0},
			ExpectError:  false,
		},
		"non-empty set, none, no error": {
			SetElts: nil,
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(s string) (optionals.Optional[int], error) {
					return optionals.None[int](), nil
				}
			},
			ExpectedElts: nil,
			ExpectError:  false,
		},
		"non-empty set, index, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				i := 0
				return func(s string) (optionals.Optional[int], error) {
					i++
					return optionals.Some(i), nil
				}
			},
			ExpectedElts: []int{1, 2, 3},
			ExpectError:  false,
		},
		"non-empty set, lengths, no error": {
			SetElts: []string{"foo", "bar", "baz", "qux", "quux"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(s string) (optionals.Optional[int], error) {
					return optionals.Some(len(s)), nil
				}
			},
			ExpectedElts: []int{3, 4},
			ExpectError:  false,
		},
		"non-empty set, last char of strings starting with b, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(s string) (optionals.Optional[int], error) {
					if strings.HasPrefix(s, "b") {
						return optionals.Some(int(s[2])), nil
					}
					return optionals.None[int](), nil
				}
			},
			ExpectedElts: []int{'r', 'z'},
			ExpectError:  false,
		},
		"non-empty set, 42, error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(s string) (optionals.Optional[int], error) {
					return optionals.Some(42), fmt.Errorf("")
				}
			},
			ExpectedElts: []int{42},
			ExpectError:  true,
		},
		"non-empty set, none, error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(s string) (optionals.Optional[int], error) {
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedElts: nil,
			ExpectError:  true,
		},
	}

	for name, tc := range testCases {
		s := sets.NewHashSet(tc.SetElts...)
		s2, err := FilterMap(s, tc.MakeFilterMap())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		// Expect that the set is unchanged.
		assert.Equal(t, sets.NewHashSet(tc.SetElts...), s, name)

		assert.Equal(t, sets.NewHashSet(tc.ExpectedElts...), s2, name)
	}
}

func TestFilterMapNoError(t *testing.T) {
	type TestCase struct {
		SetElts       []string
		MakeFilterMap func() func(string) optionals.Optional[int]
		ExpectedElts  []int
	}
	testCases := map[string]TestCase{
		"empty set, zero": {
			SetElts: nil,
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(s string) optionals.Optional[int] {
					return optionals.Some(0)
				}
			},
			ExpectedElts: nil,
		},
		"empty set, none": {
			SetElts: nil,
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(s string) optionals.Optional[int] {
					return optionals.None[int]()
				}
			},
			ExpectedElts: nil,
		},
		"non-empty set, zero": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(s string) optionals.Optional[int] {
					return optionals.Some(0)
				}
			},
			ExpectedElts: []int{0},
		},
		"non-empty set, none": {
			SetElts: nil,
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(s string) optionals.Optional[int] {
					return optionals.None[int]()
				}
			},
			ExpectedElts: nil,
		},
		"non-empty set, index": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				i := 0
				return func(s string) optionals.Optional[int] {
					i++
					return optionals.Some(i)
				}
			},
			ExpectedElts: []int{1, 2, 3},
		},
		"non-empty set, lengths": {
			SetElts: []string{"foo", "bar", "baz", "qux", "quux"},
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(s string) optionals.Optional[int] {
					return optionals.Some(len(s))
				}
			},
			ExpectedElts: []int{3, 4},
		},
		"non-empty set, last char of strings starting with b": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(s string) optionals.Optional[int] {
					if strings.HasPrefix(s, "b") {
						return optionals.Some(int(s[2]))
					}
					return optionals.None[int]()
				}
			},
			ExpectedElts: []int{'r', 'z'},
		},
	}

	for name, tc := range testCases {
		s := sets.NewHashSet(tc.SetElts...)
		s2 := FilterMapNoError(s, tc.MakeFilterMap())

		// Expect that the set is unchanged.
		assert.Equal(t, sets.NewHashSet(tc.SetElts...), s, name)

		assert.Equal(t, sets.NewHashSet(tc.ExpectedElts...), s2, name)
	}
}

func TestFold(t *testing.T) {
	type TestCase struct {
		SetElts      []string
		FoldInit     int
		MakeFoldFunc func() func(string, int) (int, error)
		Expected     int
		ExpectError  bool
	}
	testCases := map[string]TestCase{
		"empty set, set to 42, no error": {
			SetElts:  nil,
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int) (int, error) {
				return func(s string, accum int) (int, error) {
					return 42, nil
				}
			},
			Expected:    0,
			ExpectError: false,
		},
		"empty set, set to 42, error": {
			SetElts:  nil,
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int) (int, error) {
				return func(s string, accum int) (int, error) {
					return 42, fmt.Errorf("")
				}
			},
			Expected: 0,
			// Empty set, so fold function doesn't get called, so no error expected.
			ExpectError: false,
		},
		"non-empty set, set to 42, no error": {
			SetElts:  []string{"foo", "bar", "baz"},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int) (int, error) {
				return func(s string, accum int) (int, error) {
					return 42, nil
				}
			},
			Expected:    42,
			ExpectError: false,
		},
		"non-empty set, add lengths, no error": {
			SetElts:  []string{"foo", "bar", "baz", "qux", "quux"},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int) (int, error) {
				return func(s string, accum int) (int, error) {
					return accum + len(s), nil
				}
			},
			Expected:    16,
			ExpectError: false,
		},
		"non-empty set, add lengths, error": {
			SetElts:  []string{"foo", "bar", "baz"},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int) (int, error) {
				return func(s string, accum int) (int, error) {
					return accum + len(s), fmt.Errorf("")
				}
			},
			Expected:    3,
			ExpectError: true,
		},
	}

	for name, tc := range testCases {
		s := sets.NewHashSet(tc.SetElts...)
		actual, err := Fold(s, tc.FoldInit, tc.MakeFoldFunc())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		// Expect that the set is unchanged.
		assert.Equal(t, sets.NewHashSet(tc.SetElts...), s, name)

		assert.Equal(t, actual, tc.Expected, name)
	}
}

func TestFoldNoError(t *testing.T) {
	type TestCase struct {
		SetElts      []string
		FoldInit     int
		MakeFoldFunc func() func(string, int) int
		Expected     int
	}
	testCases := map[string]TestCase{
		"empty set, set to 42": {
			SetElts:  nil,
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int) int {
				return func(s string, accum int) int {
					return 42
				}
			},
			Expected: 0,
		},
		"non-empty set, set to 42": {
			SetElts:  []string{"foo", "bar", "baz"},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int) int {
				return func(s string, accum int) int {
					return 42
				}
			},
			Expected: 42,
		},
		"non-empty set, add lengths": {
			SetElts:  []string{"foo", "bar", "baz", "qux", "quux"},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int) int {
				return func(s string, accum int) int {
					return accum + len(s)
				}
			},
			Expected: 16,
		},
	}

	for name, tc := range testCases {
		s := sets.NewHashSet(tc.SetElts...)
		actual := FoldNoError(s, tc.FoldInit, tc.MakeFoldFunc())

		// Expect that the set is unchanged.
		assert.Equal(t, sets.NewHashSet(tc.SetElts...), s, name)

		assert.Equal(t, actual, tc.Expected, name)
	}
}

func TestMap(t *testing.T) {
	type TestCase struct {
		SetElts      []string
		MakeMap      func() func(string) (int, error)
		ExpectedElts []int
		ExpectError  bool
	}
	testCases := map[string]TestCase{
		"empty set, zero, no error": {
			SetElts: nil,
			MakeMap: func() func(string) (int, error) {
				return func(s string) (int, error) {
					return 0, nil
				}
			},
			ExpectedElts: nil,
			ExpectError:  false,
		},
		"empty set, zero, error": {
			SetElts: nil,
			MakeMap: func() func(string) (int, error) {
				return func(s string) (int, error) {
					return 0, fmt.Errorf("")
				}
			},
			ExpectedElts: nil,
			// Empty set, so filter/map function doesn't get called, so no error
			// expected.
			ExpectError: false,
		},
		"non-empty set, zero, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeMap: func() func(string) (int, error) {
				return func(s string) (int, error) {
					return 0, nil
				}
			},
			ExpectedElts: []int{0},
			ExpectError:  false,
		},
		"non-empty set, index, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeMap: func() func(string) (int, error) {
				i := 0
				return func(s string) (int, error) {
					i++
					return i, nil
				}
			},
			ExpectedElts: []int{1, 2, 3},
			ExpectError:  false,
		},
		"non-empty set, lengths, no error": {
			SetElts: []string{"foo", "bar", "baz", "qux", "quux"},
			MakeMap: func() func(string) (int, error) {
				return func(s string) (int, error) {
					return len(s), nil
				}
			},
			ExpectedElts: []int{3, 4},
			ExpectError:  false,
		},
		"non-empty set, last char, no error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeMap: func() func(string) (int, error) {
				return func(s string) (int, error) {
					return int(s[2]), nil
				}
			},
			ExpectedElts: []int{'o', 'r', 'z'},
			ExpectError:  false,
		},
		"non-empty set, 42, error": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeMap: func() func(string) (int, error) {
				return func(s string) (int, error) {
					return 42, fmt.Errorf("")
				}
			},
			ExpectedElts: nil,
			ExpectError:  true,
		},
		"non-empty set, indexes, error on second element": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeMap: func() func(string) (int, error) {
				i := 0
				return func(s string) (int, error) {
					i++
					if i < 2 {
						return i, nil
					}
					return i, fmt.Errorf("")
				}
			},
			ExpectedElts: []int{1},
			ExpectError:  true,
		},
	}

	for name, tc := range testCases {
		s := sets.NewHashSet(tc.SetElts...)
		s2, err := Map(s, tc.MakeMap())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		// Expect that the set is unchanged.
		assert.Equal(t, sets.NewHashSet(tc.SetElts...), s, name)

		assert.Equal(t, sets.NewHashSet(tc.ExpectedElts...), s2, name)
	}
}

func TestMapNoError(t *testing.T) {
	type TestCase struct {
		SetElts      []string
		MakeMap      func() func(string) int
		ExpectedElts []int
	}
	testCases := map[string]TestCase{
		"empty set, zero": {
			SetElts: nil,
			MakeMap: func() func(string) int {
				return func(s string) int {
					return 0
				}
			},
			ExpectedElts: nil,
		},
		"non-empty set, zero": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeMap: func() func(string) int {
				return func(s string) int {
					return 0
				}
			},
			ExpectedElts: []int{0},
		},
		"non-empty set, index": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeMap: func() func(string) int {
				i := 0
				return func(s string) int {
					i++
					return i
				}
			},
			ExpectedElts: []int{1, 2, 3},
		},
		"non-empty set, lengths": {
			SetElts: []string{"foo", "bar", "baz", "qux", "quux"},
			MakeMap: func() func(string) int {
				return func(s string) int {
					return len(s)
				}
			},
			ExpectedElts: []int{3, 4},
		},
		"non-empty set, last char": {
			SetElts: []string{"foo", "bar", "baz"},
			MakeMap: func() func(string) int {
				return func(s string) int {
					return int(s[2])
				}
			},
			ExpectedElts: []int{'o', 'r', 'z'},
		},
	}

	for name, tc := range testCases {
		s := sets.NewHashSet(tc.SetElts...)
		s2 := MapNoError(s, tc.MakeMap())

		// Expect that the set is unchanged.
		assert.Equal(t, sets.NewHashSet(tc.SetElts...), s, name)

		assert.Equal(t, sets.NewHashSet(tc.ExpectedElts...), s2, name)
	}
}
