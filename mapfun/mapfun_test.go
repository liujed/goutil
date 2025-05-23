package mapfun

import (
	"fmt"
	"strings"
	"testing"

	"github.com/liujed/goutil/maps"
	"github.com/liujed/goutil/optionals"
	"github.com/stretchr/testify/assert"
)

func TestFilter(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]int
		MakePredicate func() func(string, int) (bool, error)
		// If given, then an assertion will be made about the resulting map's
		// contents.
		ExpectedMap optionals.Optional[map[string]int]
		// Automatically filled in if ExpectedMap is given.
		ExpectedSize int
		ExpectError  bool
	}
	testCases := map[string]TestCase{
		"empty map, true, no error": {
			InitialMap: nil,
			MakePredicate: func() func(string, int) (bool, error) {
				return func(s string, i int) (bool, error) {
					return true, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, false, no error": {
			InitialMap: nil,
			MakePredicate: func() func(string, int) (bool, error) {
				return func(s string, i int) (bool, error) {
					return false, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, true, error": {
			InitialMap: nil,
			MakePredicate: func() func(string, int) (bool, error) {
				return func(s string, i int) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"empty map, false, error": {
			InitialMap: nil,
			MakePredicate: func() func(string, int) (bool, error) {
				return func(s string, i int) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"non-empty map, true, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) (bool, error) {
				return func(s string, i int) (bool, error) {
					return true, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 1, "bar": 2, "baz": 3,
			}),
			ExpectError: false,
		},
		"non-empty map, false, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) (bool, error) {
				return func(s string, i int) (bool, error) {
					return false, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"non-empty map, key starts with b, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) (bool, error) {
				return func(s string, i int) (bool, error) {
					return strings.HasPrefix(s, "b"), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"bar": 2, "baz": 3}),
			ExpectError: false,
		},
		"non-empty map, value is even, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) (bool, error) {
				return func(s string, i int) (bool, error) {
					return i%2 == 0, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"bar": 2}),
			ExpectError: false,
		},
		"non-empty map, true, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) (bool, error) {
				return func(s string, i int) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			// Expect the first entry to be added.
			ExpectedSize: 1,
			ExpectError:  true,
		},
		"non-empty map, false, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) (bool, error) {
				return func(s string, i int) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: true,
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		m2, err := Filter(m, tc.MakePredicate())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			assert.Equal(t, maps.FromGo(expectedMap), m2, name)
		}

		assert.Equal(t, tc.ExpectedSize, m2.Size(), name)
	}
}

func TestFilterNoError(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]int
		MakePredicate func() func(string, int) bool
		ExpectedMap   map[string]int
	}
	testCases := map[string]TestCase{
		"empty map, true": {
			InitialMap: nil,
			MakePredicate: func() func(string, int) bool {
				return func(s string, i int) bool {
					return true
				}
			},
			ExpectedMap: nil,
		},
		"empty map, false": {
			InitialMap: nil,
			MakePredicate: func() func(string, int) bool {
				return func(s string, i int) bool {
					return false
				}
			},
			ExpectedMap: nil,
		},
		"non-empty map, true": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) bool {
				return func(s string, i int) bool {
					return true
				}
			},
			ExpectedMap: map[string]int{
				"foo": 1, "bar": 2, "baz": 3,
			},
		},
		"non-empty map, false": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) bool {
				return func(s string, i int) bool {
					return false
				}
			},
			ExpectedMap: nil,
		},
		"non-empty map, key starts with b": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) bool {
				return func(s string, i int) bool {
					return strings.HasPrefix(s, "b")
				}
			},
			ExpectedMap: map[string]int{"bar": 2, "baz": 3},
		},
		"non-empty map, value is even": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) bool {
				return func(s string, i int) bool {
					return i%2 == 0
				}
			},
			ExpectedMap: map[string]int{"bar": 2},
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		m2 := FilterNoError(m, tc.MakePredicate())

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		assert.Equal(t, maps.FromGo(tc.ExpectedMap), m2, name)
	}
}

func TestFilterKeys(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]int
		MakePredicate func() func(string) (bool, error)
		// If given, then an assertion will be made about the resulting map's
		// contents.
		ExpectedMap optionals.Optional[map[string]int]
		// Automatically filled in if ExpectedMap is given.
		ExpectedSize int
		ExpectError  bool
	}
	testCases := map[string]TestCase{
		"empty map, true, no error": {
			InitialMap: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, false, no error": {
			InitialMap: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, true, error": {
			InitialMap: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"empty map, false, error": {
			InitialMap: nil,
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"non-empty map, true, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 1, "bar": 2, "baz": 3,
			}),
			ExpectError: false,
		},
		"non-empty map, false, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"non-empty map, key starts with b, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return strings.HasPrefix(s, "b"), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"bar": 2, "baz": 3}),
			ExpectError: false,
		},
		"non-empty map, true, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			// Expect the first entry to be added.
			ExpectedSize: 1,
			ExpectError:  true,
		},
		"non-empty map, false, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: true,
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		m2, err := FilterKeys(m, tc.MakePredicate())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			assert.Equal(t, maps.FromGo(expectedMap), m2, name)
		}

		assert.Equal(t, tc.ExpectedSize, m2.Size(), name)
	}
}

func TestFilterKeysNoError(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]int
		MakePredicate func() func(string) bool
		ExpectedMap   map[string]int
	}
	testCases := map[string]TestCase{
		"empty map, true": {
			InitialMap: nil,
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return true
				}
			},
			ExpectedMap: nil,
		},
		"empty map, false": {
			InitialMap: nil,
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return false
				}
			},
			ExpectedMap: nil,
		},
		"non-empty map, true": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return true
				}
			},
			ExpectedMap: map[string]int{
				"foo": 1, "bar": 2, "baz": 3,
			},
		},
		"non-empty map, false": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return false
				}
			},
			ExpectedMap: nil,
		},
		"non-empty map, key starts with b": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string) bool {
				return func(s string) bool {
					return strings.HasPrefix(s, "b")
				}
			},
			ExpectedMap: map[string]int{"bar": 2, "baz": 3},
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		m2 := FilterKeysNoError(m, tc.MakePredicate())

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		assert.Equal(t, maps.FromGo(tc.ExpectedMap), m2, name)
	}
}

func TestFilterValues(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]int
		MakePredicate func() func(int) (bool, error)
		// If given, then an assertion will be made about the resulting map's
		// contents.
		ExpectedMap optionals.Optional[map[string]int]
		// Automatically filled in if ExpectedMap is given.
		ExpectedSize int
		ExpectError  bool
	}
	testCases := map[string]TestCase{
		"empty map, true, no error": {
			InitialMap: nil,
			MakePredicate: func() func(int) (bool, error) {
				return func(i int) (bool, error) {
					return true, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, false, no error": {
			InitialMap: nil,
			MakePredicate: func() func(int) (bool, error) {
				return func(i int) (bool, error) {
					return false, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, true, error": {
			InitialMap: nil,
			MakePredicate: func() func(int) (bool, error) {
				return func(i int) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"empty map, false, error": {
			InitialMap: nil,
			MakePredicate: func() func(int) (bool, error) {
				return func(i int) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so predicate doesn't get called, so no error expected.
			ExpectError: false,
		},
		"non-empty map, true, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(int) (bool, error) {
				return func(i int) (bool, error) {
					return true, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 1, "bar": 2, "baz": 3,
			}),
			ExpectError: false,
		},
		"non-empty map, false, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(int) (bool, error) {
				return func(i int) (bool, error) {
					return false, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"non-empty map, value is even, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(int) (bool, error) {
				return func(i int) (bool, error) {
					return i%2 == 0, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"bar": 2}),
			ExpectError: false,
		},
		"non-empty map, true, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(int) (bool, error) {
				return func(i int) (bool, error) {
					return true, fmt.Errorf("")
				}
			},
			// Expect the first entry to be added.
			ExpectedSize: 1,
			ExpectError:  true,
		},
		"non-empty map, false, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(int) (bool, error) {
				return func(i int) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: true,
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		m2, err := FilterValues(m, tc.MakePredicate())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			assert.Equal(t, maps.FromGo(expectedMap), m2, name)
		}

		assert.Equal(t, tc.ExpectedSize, m2.Size(), name)
	}
}

func TestFilterValuesNoError(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]int
		MakePredicate func() func(int) bool
		ExpectedMap   map[string]int
	}
	testCases := map[string]TestCase{
		"empty map, true": {
			InitialMap: nil,
			MakePredicate: func() func(int) bool {
				return func(i int) bool {
					return true
				}
			},
			ExpectedMap: nil,
		},
		"empty map, false": {
			InitialMap: nil,
			MakePredicate: func() func(int) bool {
				return func(i int) bool {
					return false
				}
			},
			ExpectedMap: nil,
		},
		"non-empty map, true": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(int) bool {
				return func(i int) bool {
					return true
				}
			},
			ExpectedMap: map[string]int{
				"foo": 1, "bar": 2, "baz": 3,
			},
		},
		"non-empty map, false": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(int) bool {
				return func(i int) bool {
					return false
				}
			},
			ExpectedMap: nil,
		},
		"non-empty map, value is even": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(int) bool {
				return func(i int) bool {
					return i%2 == 0
				}
			},
			ExpectedMap: map[string]int{"bar": 2},
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		m2 := FilterValuesNoError(m, tc.MakePredicate())

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		assert.Equal(t, maps.FromGo(tc.ExpectedMap), m2, name)
	}
}

func TestFilterMap(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]string
		MakeFilterMap func() func(string, string) (optionals.Optional[int], error)
		// If given, then an assertion will be made about the resulting map's
		// contents.
		ExpectedMap optionals.Optional[map[string]int]
		// Automatically filled in if ExpectedMap is given.
		ExpectedSize int
		// Automatically filled in if ExpectedMap is given.
		ExpectedValueSum int
		ExpectError      bool
	}
	testCases := map[string]TestCase{
		"empty map, 42, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					return optionals.Some(42), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, none, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, 42, error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					return optionals.Some(42), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so filter/map function doesn't get called, so no error
			// expected.
			ExpectError: false,
		},
		"empty map, none, error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so filter/map function doesn't get called, so no error
			// expected.
			ExpectError: false,
		},
		"non-empty map, 42, no error": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					return optionals.Some(42), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
			ExpectError: false,
		},
		"non-empty map, add 2, no error": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					return optionals.Some(int(v[0]) - '0' + 2), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
			ExpectError: false,
		},
		"non-empty map, none, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"non-empty map, index, no error": {
			InitialMap: map[string]string{"foo": "0", "bar": "0", "baz": "0"},
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				i := 0
				return func(k string, v string) (optionals.Optional[int], error) {
					i++
					return optionals.Some(i), nil
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
			ExpectError:      false,
		},
		"non-empty map, key lengths, no error": {
			InitialMap: map[string]string{
				"foo": "1", "bar": "2", "baz": "3", "qux": "4", "quux": "5",
			},
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					return optionals.Some(len(k)), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 3, "baz": 3, "qux": 3, "quux": 4,
			}),
			ExpectError: false,
		},
		"non-empty map, last char of keys starting with b, no error": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					if strings.HasPrefix(k, "b") {
						return optionals.Some(int(k[2])), nil
					}
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"bar": 'r', "baz": 'z',
			}),
			ExpectError: false,
		},
		"non-empty map, first byte of values whose keys start with b, no error": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					if strings.HasPrefix(k, "b") {
						return optionals.Some(int(v[0])), nil
					}
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"bar": '2', "baz": '3',
			}),
			ExpectError: false,
		},
		"non-empty map, double first byte of odd values, no error": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					if v[0]%2 == 1 {
						return optionals.Some(2 * int(v[0])), nil
					}
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 2 * '1', "baz": 2 * '3',
			}),
			ExpectError: false,
		},
		"non-empty map, 42, error": {
			InitialMap: map[string]string{"foo": "1", "bar": "1", "baz": "1"},
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					return optionals.Some(42), fmt.Errorf("")
				}
			},
			ExpectedSize:     1,
			ExpectedValueSum: 42,
			ExpectError:      true,
		},
		"non-empty map, 42, error on second entry": {
			InitialMap: map[string]string{"foo": "1", "bar": "1", "baz": "1"},
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				i := 0
				return func(k string, v string) (optionals.Optional[int], error) {
					i++
					if i < 2 {
						return optionals.Some(42), nil
					}
					return optionals.Some(42), fmt.Errorf("")
				}
			},
			ExpectedSize:     2,
			ExpectedValueSum: 2 * 42,
			ExpectError:      true,
		},
		"non-empty map, none, error": {
			InitialMap: map[string]string{"foo": "1", "bar": "1", "baz": "1"},
			MakeFilterMap: func() func(string, string) (optionals.Optional[int], error) {
				return func(k string, v string) (optionals.Optional[int], error) {
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: true,
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, string]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		m2, err := FilterMap(m, tc.MakeFilterMap())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, maps.FromGo(expectedMap), m2, name)
		}

		assert.Equal(t, tc.ExpectedSize, m2.Size(), name)

		actualSum := 0
		for _, v := range m2.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}

func TestFilterMapNoError(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]string
		MakeFilterMap func() func(string, string) optionals.Optional[int]
		// If given, then an assertion will be made about the resulting map's
		// contents.
		ExpectedMap optionals.Optional[map[string]int]
		// Automatically filled in if ExpectedMap is given.
		ExpectedSize int
		// Automatically filled in if ExpectedMap is given.
		ExpectedValueSum int
	}
	testCases := map[string]TestCase{
		"empty map, 42": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, string) optionals.Optional[int] {
				return func(k string, v string) optionals.Optional[int] {
					return optionals.Some(42)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"empty map, none": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, string) optionals.Optional[int] {
				return func(k string, v string) optionals.Optional[int] {
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"non-empty map, 42": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string, string) optionals.Optional[int] {
				return func(k string, v string) optionals.Optional[int] {
					return optionals.Some(42)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
		},
		"non-empty map, add 2": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string, string) optionals.Optional[int] {
				return func(k string, v string) optionals.Optional[int] {
					return optionals.Some(int(v[0]) - '0' + 2)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
		},
		"non-empty map, none": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, string) optionals.Optional[int] {
				return func(k string, v string) optionals.Optional[int] {
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"non-empty map, index": {
			InitialMap: map[string]string{"foo": "0", "bar": "0", "baz": "0"},
			MakeFilterMap: func() func(string, string) optionals.Optional[int] {
				i := 0
				return func(k string, v string) optionals.Optional[int] {
					i++
					return optionals.Some(i)
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
		},
		"non-empty map, key lengths": {
			InitialMap: map[string]string{
				"foo": "1", "bar": "2", "baz": "3", "qux": "4", "quux": "5",
			},
			MakeFilterMap: func() func(string, string) optionals.Optional[int] {
				return func(k string, v string) optionals.Optional[int] {
					return optionals.Some(len(k))
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 3, "baz": 3, "qux": 3, "quux": 4,
			}),
		},
		"non-empty map, last char of keys starting with b": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string, string) optionals.Optional[int] {
				return func(k string, v string) optionals.Optional[int] {
					if strings.HasPrefix(k, "b") {
						return optionals.Some(int(k[2]))
					}
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"bar": 'r', "baz": 'z',
			}),
		},
		"non-empty map, first byte of values whose keys start with b": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string, string) optionals.Optional[int] {
				return func(k string, v string) optionals.Optional[int] {
					if strings.HasPrefix(k, "b") {
						return optionals.Some(int(v[0]))
					}
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"bar": '2', "baz": '3',
			}),
		},
		"non-empty map, double first byte of odd values": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string, string) optionals.Optional[int] {
				return func(k string, v string) optionals.Optional[int] {
					if v[0]%2 == 1 {
						return optionals.Some(2 * int(v[0]))
					}
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 2 * '1', "baz": 2 * '3',
			}),
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, string]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		m2 := FilterMapNoError(m, tc.MakeFilterMap())

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, maps.FromGo(expectedMap), m2, name)
		}

		assert.Equal(t, tc.ExpectedSize, m2.Size(), name)

		actualSum := 0
		for _, v := range m2.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}

func TestFilterMapValues(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]string
		MakeFilterMap func() func(string) (optionals.Optional[int], error)
		// If given, then an assertion will be made about the resulting map's
		// contents.
		ExpectedMap optionals.Optional[map[string]int]
		// Automatically filled in if ExpectedMap is given.
		ExpectedSize int
		// Automatically filled in if ExpectedMap is given.
		ExpectedValueSum int
		ExpectError      bool
	}
	testCases := map[string]TestCase{
		"empty map, 42, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(v string) (optionals.Optional[int], error) {
					return optionals.Some(42), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, none, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(v string) (optionals.Optional[int], error) {
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, 42, error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(v string) (optionals.Optional[int], error) {
					return optionals.Some(42), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so filter/map function doesn't get called, so no error
			// expected.
			ExpectError: false,
		},
		"empty map, none, error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(v string) (optionals.Optional[int], error) {
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so filter/map function doesn't get called, so no error
			// expected.
			ExpectError: false,
		},
		"non-empty map, 42, no error": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(v string) (optionals.Optional[int], error) {
					return optionals.Some(42), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
			ExpectError: false,
		},
		"non-empty map, add 2, no error": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(v string) (optionals.Optional[int], error) {
					return optionals.Some(int(v[0]) - '0' + 2), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
			ExpectError: false,
		},
		"non-empty map, none, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(v string) (optionals.Optional[int], error) {
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"non-empty map, index, no error": {
			InitialMap: map[string]string{"foo": "0", "bar": "0", "baz": "0"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				i := 0
				return func(v string) (optionals.Optional[int], error) {
					i++
					return optionals.Some(i), nil
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
			ExpectError:      false,
		},
		"non-empty map, double first byte of odd values, no error": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(v string) (optionals.Optional[int], error) {
					if v[0]%2 == 1 {
						return optionals.Some(2 * int(v[0])), nil
					}
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 2 * '1', "baz": 2 * '3',
			}),
			ExpectError: false,
		},
		"non-empty map, 42, error": {
			InitialMap: map[string]string{"foo": "1", "bar": "1", "baz": "1"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(v string) (optionals.Optional[int], error) {
					return optionals.Some(42), fmt.Errorf("")
				}
			},
			ExpectedSize:     1,
			ExpectedValueSum: 42,
			ExpectError:      true,
		},
		"non-empty map, 42, error on second entry": {
			InitialMap: map[string]string{"foo": "1", "bar": "1", "baz": "1"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				i := 0
				return func(v string) (optionals.Optional[int], error) {
					i++
					if i < 2 {
						return optionals.Some(42), nil
					}
					return optionals.Some(42), fmt.Errorf("")
				}
			},
			ExpectedSize:     2,
			ExpectedValueSum: 2 * 42,
			ExpectError:      true,
		},
		"non-empty map, none, error": {
			InitialMap: map[string]string{"foo": "1", "bar": "1", "baz": "1"},
			MakeFilterMap: func() func(string) (optionals.Optional[int], error) {
				return func(v string) (optionals.Optional[int], error) {
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: true,
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, string]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		m2, err := FilterMapValues(m, tc.MakeFilterMap())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, maps.FromGo(expectedMap), m2, name)
		}

		assert.Equal(t, tc.ExpectedSize, m2.Size(), name)

		actualSum := 0
		for _, v := range m2.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}

func TestFilterMapValuesNoError(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]string
		MakeFilterMap func() func(string) optionals.Optional[int]
		// If given, then an assertion will be made about the resulting map's
		// contents.
		ExpectedMap optionals.Optional[map[string]int]
		// Automatically filled in if ExpectedMap is given.
		ExpectedSize int
		// Automatically filled in if ExpectedMap is given.
		ExpectedValueSum int
	}
	testCases := map[string]TestCase{
		"empty map, 42": {
			InitialMap: nil,
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(v string) optionals.Optional[int] {
					return optionals.Some(42)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"empty map, none": {
			InitialMap: nil,
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(v string) optionals.Optional[int] {
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"non-empty map, 42": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(v string) optionals.Optional[int] {
					return optionals.Some(42)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
		},
		"non-empty map, add 2": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(v string) optionals.Optional[int] {
					return optionals.Some(int(v[0]) - '0' + 2)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
		},
		"non-empty map, none": {
			InitialMap: nil,
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(v string) optionals.Optional[int] {
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"non-empty map, index": {
			InitialMap: map[string]string{"foo": "0", "bar": "0", "baz": "0"},
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				i := 0
				return func(v string) optionals.Optional[int] {
					i++
					return optionals.Some(i)
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
		},
		"non-empty map, double first byte of odd values": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeFilterMap: func() func(string) optionals.Optional[int] {
				return func(v string) optionals.Optional[int] {
					if v[0]%2 == 1 {
						return optionals.Some(2 * int(v[0]))
					}
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 2 * '1', "baz": 2 * '3',
			}),
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, string]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		m2 := FilterMapValuesNoError(m, tc.MakeFilterMap())

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, maps.FromGo(expectedMap), m2, name)
		}

		assert.Equal(t, tc.ExpectedSize, m2.Size(), name)

		actualSum := 0
		for _, v := range m2.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}

func TestFold(t *testing.T) {
	type TestCase struct {
		Map          map[string]int
		FoldInit     int
		MakeFoldFunc func() func(string, int, int) (int, error)
		Expected     int
		ExpectError  bool
	}
	testCases := map[string]TestCase{
		"empty map, set to 42, no error": {
			Map:      nil,
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) (int, error) {
				return func(k string, v int, accum int) (int, error) {
					return 42, nil
				}
			},
			Expected:    0,
			ExpectError: false,
		},
		"empty map, set to 42, error": {
			Map:      nil,
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) (int, error) {
				return func(k string, v int, accum int) (int, error) {
					return 42, fmt.Errorf("")
				}
			},
			Expected: 0,
			// Empty map, so fold function doesn't get called, so no error expected.
			ExpectError: false,
		},
		"non-empty map, set to 42, no error": {
			Map:      map[string]int{"foo": 1, "bar": 2, "baz": 4},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) (int, error) {
				return func(k string, v int, accum int) (int, error) {
					return 42, nil
				}
			},
			Expected:    42,
			ExpectError: false,
		},
		"non-empty map, add key lengths, no error": {
			Map: map[string]int{
				"foo": 1, "bar": 2, "baz": 4, "qux": 8, "quux": 16,
			},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) (int, error) {
				return func(k string, v int, accum int) (int, error) {
					return accum + len(k), nil
				}
			},
			Expected:    16,
			ExpectError: false,
		},
		"non-empty map, add values, no error": {
			Map: map[string]int{
				"foo": 1, "bar": 2, "baz": 4, "qux": 8, "quux": 16,
			},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) (int, error) {
				return func(k string, v int, accum int) (int, error) {
					return accum + v, nil
				}
			},
			Expected:    31,
			ExpectError: false,
		},
		"non-empty map, add values of keys that start with q, no error": {
			Map: map[string]int{
				"foo": 1, "bar": 2, "baz": 4, "qux": 8, "quux": 16,
			},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) (int, error) {
				return func(k string, v int, accum int) (int, error) {
					if strings.HasPrefix(k, "q") {
						return accum + v, nil
					}
					return accum, nil
				}
			},
			Expected:    24,
			ExpectError: false,
		},
		"non-empty map, add lengths, error": {
			Map:      map[string]int{"foo": 1, "bar": 2, "baz": 4},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) (int, error) {
				return func(k string, v int, accum int) (int, error) {
					return accum + len(k), fmt.Errorf("")
				}
			},
			Expected:    3,
			ExpectError: true,
		},
		"non-empty map, add values, error": {
			Map:      map[string]int{"foo": 1, "bar": 1, "baz": 1},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) (int, error) {
				return func(k string, v int, accum int) (int, error) {
					return accum + v, fmt.Errorf("")
				}
			},
			Expected:    1,
			ExpectError: true,
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, int]()
		for k, v := range tc.Map {
			m.Put(k, v)
		}

		actual, err := Fold(m, tc.FoldInit, tc.MakeFoldFunc())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.Map), m, name)

		assert.Equal(t, actual, tc.Expected, name)
	}
}

func TestFoldNoError(t *testing.T) {
	type TestCase struct {
		Map          map[string]int
		FoldInit     int
		MakeFoldFunc func() func(string, int, int) int
		Expected     int
	}
	testCases := map[string]TestCase{
		"empty map, set to 42, no error": {
			Map:      nil,
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) int {
				return func(k string, v int, accum int) int {
					return 42
				}
			},
			Expected: 0,
		},
		"non-empty map, set to 42, no error": {
			Map:      map[string]int{"foo": 1, "bar": 2, "baz": 4},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) int {
				return func(k string, v int, accum int) int {
					return 42
				}
			},
			Expected: 42,
		},
		"non-empty map, add key lengths, no error": {
			Map: map[string]int{
				"foo": 1, "bar": 2, "baz": 4, "qux": 8, "quux": 16,
			},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) int {
				return func(k string, v int, accum int) int {
					return accum + len(k)
				}
			},
			Expected: 16,
		},
		"non-empty map, add values, no error": {
			Map: map[string]int{
				"foo": 1, "bar": 2, "baz": 4, "qux": 8, "quux": 16,
			},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) int {
				return func(k string, v int, accum int) int {
					return accum + v
				}
			},
			Expected: 31,
		},
		"non-empty map, add values of keys that start with q, no error": {
			Map: map[string]int{
				"foo": 1, "bar": 2, "baz": 4, "qux": 8, "quux": 16,
			},
			FoldInit: 0,
			MakeFoldFunc: func() func(string, int, int) int {
				return func(k string, v int, accum int) int {
					if strings.HasPrefix(k, "q") {
						return accum + v
					}
					return accum
				}
			},
			Expected: 24,
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, int]()
		for k, v := range tc.Map {
			m.Put(k, v)
		}

		actual := FoldNoError(m, tc.FoldInit, tc.MakeFoldFunc())

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.Map), m, name)

		assert.Equal(t, actual, tc.Expected, name)
	}
}

func TestMap(t *testing.T) {
	type TestCase struct {
		InitialMap map[string]string
		MakeMap    func() func(string) (int, error)
		// If given, then an assertion will be made about the resulting map's
		// contents.
		ExpectedMap optionals.Optional[map[string]int]
		// Automatically filled in if ExpectedMap is given.
		ExpectedSize int
		// Automatically filled in if ExpectedMap is given.
		ExpectedValueSum int
		ExpectError      bool
	}
	testCases := map[string]TestCase{
		"empty map, 42, no error": {
			InitialMap: nil,
			MakeMap: func() func(string) (int, error) {
				return func(v string) (int, error) {
					return 42, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, 42, error": {
			InitialMap: nil,
			MakeMap: func() func(string) (int, error) {
				return func(v string) (int, error) {
					return 42, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so filter/map function doesn't get called, so no error
			// expected.
			ExpectError: false,
		},
		"non-empty map, 42, no error": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeMap: func() func(string) (int, error) {
				return func(v string) (int, error) {
					return 42, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
			ExpectError: false,
		},
		"non-empty map, add 2, no error": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeMap: func() func(string) (int, error) {
				return func(v string) (int, error) {
					return int(v[0]) - '0' + 2, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
			ExpectError: false,
		},
		"non-empty map, index, no error": {
			InitialMap: map[string]string{"foo": "0", "bar": "0", "baz": "0"},
			MakeMap: func() func(string) (int, error) {
				i := 0
				return func(v string) (int, error) {
					i++
					return i, nil
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
			ExpectError:      false,
		},
		"non-empty map, 42, error": {
			InitialMap: map[string]string{"foo": "1", "bar": "1", "baz": "1"},
			MakeMap: func() func(string) (int, error) {
				return func(v string) (int, error) {
					return 42, fmt.Errorf("")
				}
			},
			ExpectedSize:     0,
			ExpectedValueSum: 0,
			ExpectError:      true,
		},
		"non-empty map, 42, error on second entry": {
			InitialMap: map[string]string{"foo": "1", "bar": "1", "baz": "1"},
			MakeMap: func() func(string) (int, error) {
				i := 0
				return func(v string) (int, error) {
					i++
					if i < 2 {
						return 42, nil
					}
					return 42, fmt.Errorf("")
				}
			},
			ExpectedSize:     1,
			ExpectedValueSum: 42,
			ExpectError:      true,
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, string]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		m2, err := Map(m, tc.MakeMap())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, maps.FromGo(expectedMap), m2, name)
		}

		assert.Equal(t, tc.ExpectedSize, m2.Size(), name)

		actualSum := 0
		for _, v := range m2.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}

func TestMapNoError(t *testing.T) {
	type TestCase struct {
		InitialMap map[string]string
		MakeMap    func() func(string) int
		// If given, then an assertion will be made about the resulting map's
		// contents.
		ExpectedMap optionals.Optional[map[string]int]
		// Automatically filled in if ExpectedMap is given.
		ExpectedSize int
		// Automatically filled in if ExpectedMap is given.
		ExpectedValueSum int
	}
	testCases := map[string]TestCase{
		"empty map, 42": {
			InitialMap: nil,
			MakeMap: func() func(string) int {
				return func(v string) int {
					return 42
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"non-empty map, 42": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeMap: func() func(string) int {
				return func(v string) int {
					return 42
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
		},
		"non-empty map, add 2": {
			InitialMap: map[string]string{"foo": "1", "bar": "2", "baz": "3"},
			MakeMap: func() func(string) int {
				return func(v string) int {
					return int(v[0]) - '0' + 2
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
		},
		"non-empty map, index": {
			InitialMap: map[string]string{"foo": "0", "bar": "0", "baz": "0"},
			MakeMap: func() func(string) int {
				i := 0
				return func(v string) int {
					i++
					return i
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
		},
	}

	for name, tc := range testCases {
		m := maps.NewHashMap[string, string]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		m2 := MapNoError(m, tc.MakeMap())

		// Expect that the map is unchanged.
		assert.Equal(t, maps.FromGo(tc.InitialMap), m, name)

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, maps.FromGo(expectedMap), m2, name)
		}

		assert.Equal(t, tc.ExpectedSize, m2.Size(), name)

		actualSum := 0
		for _, v := range m2.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}
