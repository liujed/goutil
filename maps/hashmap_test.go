package maps

import (
	"encoding/json"
	"fmt"
	"slices"
	"strings"
	"testing"

	"github.com/liujed/goutil/optionals"
	"github.com/liujed/goutil/sets"
	"github.com/stretchr/testify/assert"
)

func TestChange(t *testing.T) {
	type TestCase struct {
		InitialMap     map[string]int
		Key            string
		Func           func(optionals.Optional[int]) (optionals.Optional[int], error)
		ExpectedMap    map[string]int
		ExpectedReturn optionals.Optional[int]
		ExpectError    bool
	}
	testCases := map[string]TestCase{
		"empty map, non-member, none, no error": {
			InitialMap: nil,
			Key:        "foo",
			Func: func(o optionals.Optional[int]) (optionals.Optional[int], error) {
				assert.True(t, o.IsNone())
				return optionals.None[int](), nil
			},
			ExpectedMap:    nil,
			ExpectedReturn: optionals.None[int](),
			ExpectError:    false,
		},
		"empty map, non-member, 42, no error": {
			InitialMap: nil,
			Key:        "foo",
			Func: func(o optionals.Optional[int]) (optionals.Optional[int], error) {
				assert.True(t, o.IsNone())
				return optionals.Some(42), nil
			},
			ExpectedMap:    map[string]int{"foo": 42},
			ExpectedReturn: optionals.Some(42),
			ExpectError:    false,
		},
		"non-empty map, non-member, none, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) (optionals.Optional[int], error) {
				assert.True(t, o.IsNone())
				return optionals.None[int](), nil
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2},
			ExpectedReturn: optionals.None[int](),
			ExpectError:    false,
		},
		"non-empty map, non-member, 42, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) (optionals.Optional[int], error) {
				assert.True(t, o.IsNone())
				return optionals.Some(42), nil
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 42},
			ExpectedReturn: optionals.Some(42),
			ExpectError:    false,
		},
		"non-empty map, member, none, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) (optionals.Optional[int], error) {
				assert.True(t, o.IsSome())
				return optionals.None[int](), nil
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2},
			ExpectedReturn: optionals.None[int](),
			ExpectError:    false,
		},
		"non-empty map, member, 42, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) (optionals.Optional[int], error) {
				assert.True(t, o.IsSome())
				return optionals.Some(42), nil
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 42},
			ExpectedReturn: optionals.Some(42),
			ExpectError:    false,
		},
		"non-empty map, non-member, none, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) (optionals.Optional[int], error) {
				assert.True(t, o.IsNone())
				return optionals.None[int](), fmt.Errorf("")
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2},
			ExpectedReturn: optionals.None[int](),
			ExpectError:    true,
		},
		"non-empty map, non-member, 42, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) (optionals.Optional[int], error) {
				assert.True(t, o.IsNone())
				return optionals.Some(42), fmt.Errorf("")
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2},
			ExpectedReturn: optionals.Some(42),
			ExpectError:    true,
		},
		"non-empty map, member, none, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) (optionals.Optional[int], error) {
				assert.True(t, o.IsSome())
				return optionals.None[int](), fmt.Errorf("")
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 3},
			ExpectedReturn: optionals.None[int](),
			ExpectError:    true,
		},
		"non-empty map, member, 42, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) (optionals.Optional[int], error) {
				assert.True(t, o.IsSome())
				return optionals.Some(42), fmt.Errorf("")
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 3},
			ExpectedReturn: optionals.Some(42),
			ExpectError:    true,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		vOpt, err := m.Change(tc.Key, tc.Func)

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		assert.Equal(t, tc.ExpectedReturn, vOpt, name)
		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
	}
}

func TestChangeNoError(t *testing.T) {
	type TestCase struct {
		InitialMap     map[string]int
		Key            string
		Func           func(optionals.Optional[int]) optionals.Optional[int]
		ExpectedMap    map[string]int
		ExpectedReturn optionals.Optional[int]
	}
	testCases := map[string]TestCase{
		"empty map, non-member, none": {
			InitialMap: nil,
			Key:        "foo",
			Func: func(o optionals.Optional[int]) optionals.Optional[int] {
				assert.True(t, o.IsNone())
				return optionals.None[int]()
			},
			ExpectedMap:    nil,
			ExpectedReturn: optionals.None[int](),
		},
		"empty map, non-member, 42": {
			InitialMap: nil,
			Key:        "foo",
			Func: func(o optionals.Optional[int]) optionals.Optional[int] {
				assert.True(t, o.IsNone())
				return optionals.Some(42)
			},
			ExpectedMap:    map[string]int{"foo": 42},
			ExpectedReturn: optionals.Some(42),
		},
		"non-empty map, non-member, none": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) optionals.Optional[int] {
				assert.True(t, o.IsNone())
				return optionals.None[int]()
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2},
			ExpectedReturn: optionals.None[int](),
		},
		"non-empty map, non-member, 42": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) optionals.Optional[int] {
				assert.True(t, o.IsNone())
				return optionals.Some(42)
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 42},
			ExpectedReturn: optionals.Some(42),
		},
		"non-empty map, member, none": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) optionals.Optional[int] {
				assert.True(t, o.IsSome())
				return optionals.None[int]()
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2},
			ExpectedReturn: optionals.None[int](),
		},
		"non-empty map, member, 42": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func(o optionals.Optional[int]) optionals.Optional[int] {
				assert.True(t, o.IsSome())
				return optionals.Some(42)
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 42},
			ExpectedReturn: optionals.Some(42),
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		vOpt := m.ChangeNoError(tc.Key, tc.Func)

		assert.Equal(t, tc.ExpectedReturn, vOpt, name)
		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
	}
}

func TestClear(t *testing.T) {
	type TestCase struct {
		InitialMap map[string]int
	}
	testCases := map[string]TestCase{
		"empty map": {
			InitialMap: nil,
		},
		"non-empty map": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		m.Clear()

		// Should end up with an empty map.
		assert.Equal(t, NewHashMap[string, int](), m, name)
	}
}

func TestComputeIfAbsent(t *testing.T) {
	type TestCase struct {
		InitialMap     map[string]int
		Key            string
		Func           func() (int, error)
		ExpectedMap    map[string]int
		ExpectedReturn int
		ExpectError    bool
	}
	testCases := map[string]TestCase{
		"empty map, non-member, no error": {
			InitialMap: nil,
			Key:        "foo",
			Func: func() (int, error) {
				return 42, nil
			},
			ExpectedMap:    map[string]int{"foo": 42},
			ExpectedReturn: 42,
			ExpectError:    false,
		},
		"empty map, non-member, error": {
			InitialMap: nil,
			Key:        "foo",
			Func: func() (int, error) {
				return 42, fmt.Errorf("")
			},
			ExpectedMap:    nil,
			ExpectedReturn: 42,
			ExpectError:    true,
		},
		"non-empty map, non-member, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func() (int, error) {
				return 42, nil
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 42},
			ExpectedReturn: 42,
			ExpectError:    false,
		},
		"non-empty map, non-member, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func() (int, error) {
				return 42, fmt.Errorf("")
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2},
			ExpectedReturn: 42,
			ExpectError:    true,
		},
		"non-empty map, member, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func() (int, error) {
				return 42, nil
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 3},
			ExpectedReturn: 3,
			ExpectError:    false,
		},
		"non-empty map, member, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func() (int, error) {
				return 42, fmt.Errorf("")
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 3},
			ExpectedReturn: 3,
			ExpectError:    false,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		actual, err := m.ComputeIfAbsent(tc.Key, tc.Func)

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
		assert.Equal(t, tc.ExpectedReturn, actual, name)
	}
}

func TestComputeIfAbsentNoError(t *testing.T) {
	type TestCase struct {
		InitialMap     map[string]int
		Key            string
		Func           func() int
		ExpectedMap    map[string]int
		ExpectedReturn int
	}
	testCases := map[string]TestCase{
		"empty map, non-member": {
			InitialMap: nil,
			Key:        "foo",
			Func: func() int {
				return 42
			},
			ExpectedMap:    map[string]int{"foo": 42},
			ExpectedReturn: 42,
		},
		"non-empty map, non-member": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func() int {
				return 42
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 42},
			ExpectedReturn: 42,
		},
		"non-empty map, member": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func() int {
				return 42
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 3},
			ExpectedReturn: 3,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		actual := m.ComputeIfAbsentNoError(tc.Key, tc.Func)

		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
		assert.Equal(t, tc.ExpectedReturn, actual, name)
	}
}

func TestContainsKey(t *testing.T) {
	m := NewHashMap[string, int]()
	assert.False(t, m.ContainsKey("foo"))
	assert.False(t, m.ContainsKey("bar"))

	m.Put("foo", 42)
	assert.True(t, m.ContainsKey("foo"))
	assert.False(t, m.ContainsKey("bar"))

	m.Remove("foo")
	assert.False(t, m.ContainsKey("foo"))
	assert.False(t, m.ContainsKey("bar"))
}

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
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 1, "bar": 2, "baz": 3,
			}),
			ExpectError: true,
		},
		"non-empty map, false, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) (bool, error) {
				return func(s string, i int) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"foo": 1, "bar": 2, "baz": 3}),
			ExpectError: true,
		},
		"non-empty map, false, error on second entry": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string, int) (bool, error) {
				i := 0
				return func(s string, _ int) (bool, error) {
					i++
					if i < 2 {
						return false, nil
					}
					return false, fmt.Errorf("")
				}
			},
			// Expect the first element to be removed from the map.
			ExpectedSize: 2,
			ExpectError:  true,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		err := m.Filter(tc.MakePredicate())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			assert.Equal(t, FromGo(expectedMap), m, name)
		}

		assert.Equal(t, tc.ExpectedSize, m.Size(), name)
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
			ExpectedMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
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
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		m.FilterNoError(tc.MakePredicate())

		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
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
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 1, "bar": 2, "baz": 3,
			}),
			ExpectError: true,
		},
		"non-empty map, false, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(string) (bool, error) {
				return func(s string) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"foo": 1, "bar": 2, "baz": 3}),
			ExpectError: true,
		},
		"non-empty map, false, error on second entry": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
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
			// Expect the first element to be removed from the map.
			ExpectedSize: 2,
			ExpectError:  true,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		err := m.FilterKeys(tc.MakePredicate())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			assert.Equal(t, FromGo(expectedMap), m, name)
		}

		assert.Equal(t, tc.ExpectedSize, m.Size(), name)
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
			ExpectedMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
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
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		m.FilterKeysNoError(tc.MakePredicate())

		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
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
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 1, "bar": 2, "baz": 3,
			}),
			ExpectError: true,
		},
		"non-empty map, false, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(int) (bool, error) {
				return func(i int) (bool, error) {
					return false, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"foo": 1, "bar": 2, "baz": 3}),
			ExpectError: true,
		},
		"non-empty map, false, error on second entry": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakePredicate: func() func(int) (bool, error) {
				i := 0
				return func(int) (bool, error) {
					i++
					if i < 2 {
						return false, nil
					}
					return false, fmt.Errorf("")
				}
			},
			// Expect the first element to be removed from the map.
			ExpectedSize: 2,
			ExpectError:  true,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		err := m.FilterValues(tc.MakePredicate())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			assert.Equal(t, FromGo(expectedMap), m, name)
		}

		assert.Equal(t, tc.ExpectedSize, m.Size(), name)
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
			ExpectedMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
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
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}
		m.FilterValuesNoError(tc.MakePredicate())

		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
	}
}

func TestFilterMap(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]int
		MakeFilterMap func() func(string, int) (optionals.Optional[int], error)
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
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				return func(s string, i int) (optionals.Optional[int], error) {
					return optionals.Some(42), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, none, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				return func(s string, i int) (optionals.Optional[int], error) {
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, 42, error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				return func(s string, i int) (optionals.Optional[int], error) {
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
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				return func(s string, i int) (optionals.Optional[int], error) {
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so filter/map function doesn't get called, so no error
			// expected.
			ExpectError: false,
		},
		"non-empty map, 42, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				return func(s string, i int) (optionals.Optional[int], error) {
					return optionals.Some(42), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
			ExpectError: false,
		},
		"non-empty map, add 2, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				return func(s string, i int) (optionals.Optional[int], error) {
					return optionals.Some(i + 2), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
			ExpectError: false,
		},
		"non-empty map, none, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				return func(s string, i int) (optionals.Optional[int], error) {
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"non-empty map, index, no error": {
			InitialMap: map[string]int{"foo": 0, "bar": 0, "baz": 0},
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				i := 0
				return func(s string, _ int) (optionals.Optional[int], error) {
					i++
					return optionals.Some(i), nil
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
			ExpectError:      false,
		},
		"non-empty map, lengths, no error": {
			InitialMap: map[string]int{
				"foo": 1, "bar": 2, "baz": 3, "qux": 4, "quux": 5,
			},
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				return func(s string, i int) (optionals.Optional[int], error) {
					return optionals.Some(len(s)), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 3, "baz": 3, "qux": 3, "quux": 4,
			}),
			ExpectError: false,
		},
		"non-empty map, last char of strings starting with b, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				return func(s string, i int) (optionals.Optional[int], error) {
					if strings.HasPrefix(s, "b") {
						return optionals.Some(int(s[2])), nil
					}
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"bar": 'r', "baz": 'z',
			}),
			ExpectError: false,
		},
		"non-empty map, 42, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 1, "baz": 1},
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				return func(s string, i int) (optionals.Optional[int], error) {
					return optionals.Some(42), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"foo": 1, "bar": 1, "baz": 1}),
			ExpectError: true,
		},
		"non-empty map, 42, error on second entry": {
			InitialMap: map[string]int{"foo": 1, "bar": 1, "baz": 1},
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				i := 0
				return func(string, int) (optionals.Optional[int], error) {
					i++
					if i < 2 {
						return optionals.Some(42), nil
					}
					return optionals.Some(42), fmt.Errorf("")
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 44,
			ExpectError:      true,
		},
		"non-empty map, none, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 1, "baz": 1},
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				return func(s string, i int) (optionals.Optional[int], error) {
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"foo": 1, "bar": 1, "baz": 1}),
			ExpectError: true,
		},
		"non-empty map, none, error on second entry": {
			InitialMap: map[string]int{"foo": 1, "bar": 1, "baz": 1},
			MakeFilterMap: func() func(string, int) (optionals.Optional[int], error) {
				i := 0
				return func(string, int) (optionals.Optional[int], error) {
					i++
					if i < 2 {
						return optionals.None[int](), nil
					}
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedSize:     2,
			ExpectedValueSum: 2,
			ExpectError:      true,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		err := m.FilterMap(tc.MakeFilterMap())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, FromGo(expectedMap), m, name)
		}

		assert.Equal(t, tc.ExpectedSize, m.Size(), name)

		actualSum := 0
		for _, v := range m.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}

func TestFilterMapNoError(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]int
		MakeFilterMap func() func(string, int) optionals.Optional[int]
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
			MakeFilterMap: func() func(string, int) optionals.Optional[int] {
				return func(s string, i int) optionals.Optional[int] {
					return optionals.Some(42)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"empty map, none": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, int) optionals.Optional[int] {
				return func(s string, i int) optionals.Optional[int] {
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"non-empty map, 42": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeFilterMap: func() func(string, int) optionals.Optional[int] {
				return func(s string, i int) optionals.Optional[int] {
					return optionals.Some(42)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
		},
		"non-empty map, add 2": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeFilterMap: func() func(string, int) optionals.Optional[int] {
				return func(s string, i int) optionals.Optional[int] {
					return optionals.Some(i + 2)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
		},
		"non-empty map, none": {
			InitialMap: nil,
			MakeFilterMap: func() func(string, int) optionals.Optional[int] {
				return func(s string, i int) optionals.Optional[int] {
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"non-empty map, index": {
			InitialMap: map[string]int{"foo": 0, "bar": 0, "baz": 0},
			MakeFilterMap: func() func(string, int) optionals.Optional[int] {
				i := 0
				return func(s string, _ int) optionals.Optional[int] {
					i++
					return optionals.Some(i)
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
		},
		"non-empty map, lengths": {
			InitialMap: map[string]int{
				"foo": 1, "bar": 2, "baz": 3, "qux": 4, "quux": 5,
			},
			MakeFilterMap: func() func(string, int) optionals.Optional[int] {
				return func(s string, i int) optionals.Optional[int] {
					return optionals.Some(len(s))
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 3, "baz": 3, "qux": 3, "quux": 4,
			}),
		},
		"non-empty map, last char of strings starting with b": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeFilterMap: func() func(string, int) optionals.Optional[int] {
				return func(s string, i int) optionals.Optional[int] {
					if strings.HasPrefix(s, "b") {
						return optionals.Some(int(s[2]))
					}
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"bar": 'r', "baz": 'z',
			}),
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		m.FilterMapNoError(tc.MakeFilterMap())

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, FromGo(expectedMap), m, name)
		}

		assert.Equal(t, tc.ExpectedSize, m.Size(), name)

		actualSum := 0
		for _, v := range m.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}

func TestFilterMapValues(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]int
		MakeFilterMap func() func(int) (optionals.Optional[int], error)
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
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				return func(i int) (optionals.Optional[int], error) {
					return optionals.Some(42), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, none, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				return func(i int) (optionals.Optional[int], error) {
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, 42, error": {
			InitialMap: nil,
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				return func(i int) (optionals.Optional[int], error) {
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
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				return func(i int) (optionals.Optional[int], error) {
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so filter/map function doesn't get called, so no error
			// expected.
			ExpectError: false,
		},
		"non-empty map, 42, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				return func(i int) (optionals.Optional[int], error) {
					return optionals.Some(42), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
			ExpectError: false,
		},
		"non-empty map, add 2, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				return func(i int) (optionals.Optional[int], error) {
					return optionals.Some(i + 2), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
			ExpectError: false,
		},
		"non-empty map, none, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				return func(i int) (optionals.Optional[int], error) {
					return optionals.None[int](), nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"non-empty map, index, no error": {
			InitialMap: map[string]int{"foo": 0, "bar": 0, "baz": 0},
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				i := 0
				return func(int) (optionals.Optional[int], error) {
					i++
					return optionals.Some(i), nil
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
			ExpectError:      false,
		},
		"non-empty map, 42, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 1, "baz": 1},
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				return func(i int) (optionals.Optional[int], error) {
					return optionals.Some(42), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"foo": 1, "bar": 1, "baz": 1}),
			ExpectError: true,
		},
		"non-empty map, 42, error on second entry": {
			InitialMap: map[string]int{"foo": 1, "bar": 1, "baz": 1},
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				i := 0
				return func(int) (optionals.Optional[int], error) {
					i++
					if i < 2 {
						return optionals.Some(42), nil
					}
					return optionals.Some(42), fmt.Errorf("")
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 44,
			ExpectError:      true,
		},
		"non-empty map, none, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 1, "baz": 1},
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				return func(i int) (optionals.Optional[int], error) {
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"foo": 1, "bar": 1, "baz": 1}),
			ExpectError: true,
		},
		"non-empty map, none, error on second entry": {
			InitialMap: map[string]int{"foo": 1, "bar": 1, "baz": 1},
			MakeFilterMap: func() func(int) (optionals.Optional[int], error) {
				i := 0
				return func(int) (optionals.Optional[int], error) {
					i++
					if i < 2 {
						return optionals.None[int](), nil
					}
					return optionals.None[int](), fmt.Errorf("")
				}
			},
			ExpectedSize:     2,
			ExpectedValueSum: 2,
			ExpectError:      true,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		err := m.FilterMapValues(tc.MakeFilterMap())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, FromGo(expectedMap), m, name)
		}

		assert.Equal(t, tc.ExpectedSize, m.Size(), name)

		actualSum := 0
		for _, v := range m.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}

func TestFilterMapValuesNoError(t *testing.T) {
	type TestCase struct {
		InitialMap    map[string]int
		MakeFilterMap func() func(int) optionals.Optional[int]
		// If given, then an assertion will be made about the resulting map's
		// contents.
		ExpectedMap optionals.Optional[map[string]int]
		// Automatically filled in if ExpectedMap is given.
		ExpectedSize int
		// Automatically filled in if ExpectedMap is given.
		ExpectedValueSum int
	}
	testCases := map[string]TestCase{
		"empty map, 42, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(int) optionals.Optional[int] {
				return func(i int) optionals.Optional[int] {
					return optionals.Some(42)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"empty map, none, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(int) optionals.Optional[int] {
				return func(i int) optionals.Optional[int] {
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"non-empty map, 42, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeFilterMap: func() func(int) optionals.Optional[int] {
				return func(i int) optionals.Optional[int] {
					return optionals.Some(42)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
		},
		"non-empty map, add 2, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeFilterMap: func() func(int) optionals.Optional[int] {
				return func(i int) optionals.Optional[int] {
					return optionals.Some(i + 2)
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
		},
		"non-empty map, none, no error": {
			InitialMap: nil,
			MakeFilterMap: func() func(int) optionals.Optional[int] {
				return func(i int) optionals.Optional[int] {
					return optionals.None[int]()
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"non-empty map, index, no error": {
			InitialMap: map[string]int{"foo": 0, "bar": 0, "baz": 0},
			MakeFilterMap: func() func(int) optionals.Optional[int] {
				i := 0
				return func(int) optionals.Optional[int] {
					i++
					return optionals.Some(i)
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		m.FilterMapValuesNoError(tc.MakeFilterMap())

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, FromGo(expectedMap), m, name)
		}

		assert.Equal(t, tc.ExpectedSize, m.Size(), name)

		actualSum := 0
		for _, v := range m.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}

func TestIsEmpty(t *testing.T) {
	m := NewHashMap[string, int]()
	assert.True(t, m.IsEmpty())

	m.Put("foo", 42)
	assert.False(t, m.IsEmpty())

	m.Put("bar", 1337)
	assert.False(t, m.IsEmpty())

	m.Remove("foo")
	assert.False(t, m.IsEmpty())

	m.Remove("bar")
	assert.True(t, m.IsEmpty())
}

func TestKeySet(t *testing.T) {
	m := NewHashMap[string, int]()
	assert.Equal(t, sets.NewHashSet[string](), m.KeySet())

	m.Put("foo", 42)
	m.Put("bar", 37)
	m.Put("baz", 1337)
	m.Put("bar", 9)
	assert.Equal(t, sets.NewHashSet("foo", "bar", "baz"), m.KeySet())
}

func TestMap(t *testing.T) {
	type TestCase struct {
		InitialMap map[string]int
		MakeMap    func() func(int) (int, error)
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
			MakeMap: func() func(int) (int, error) {
				return func(i int) (int, error) {
					return 42, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			ExpectError: false,
		},
		"empty map, 42, error": {
			InitialMap: nil,
			MakeMap: func() func(int) (int, error) {
				return func(i int) (int, error) {
					return 42, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
			// Empty map, so filter/map function doesn't get called, so no error
			// expected.
			ExpectError: false,
		},
		"non-empty map, 42, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeMap: func() func(int) (int, error) {
				return func(i int) (int, error) {
					return 42, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
			ExpectError: false,
		},
		"non-empty map, add 2, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeMap: func() func(int) (int, error) {
				return func(i int) (int, error) {
					return i + 2, nil
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
			ExpectError: false,
		},
		"non-empty map, index, no error": {
			InitialMap: map[string]int{"foo": 0, "bar": 0, "baz": 0},
			MakeMap: func() func(int) (int, error) {
				i := 0
				return func(int) (int, error) {
					i++
					return i, nil
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
			ExpectError:      false,
		},
		"non-empty map, 42, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 1, "baz": 1},
			MakeMap: func() func(int) (int, error) {
				return func(i int) (int, error) {
					return 42, fmt.Errorf("")
				}
			},
			ExpectedMap: optionals.Some(map[string]int{"foo": 1, "bar": 1, "baz": 1}),
			ExpectError: true,
		},
		"non-empty map, 42, error on second value": {
			InitialMap: map[string]int{"foo": 1, "bar": 1, "baz": 1},
			MakeMap: func() func(int) (int, error) {
				i := 0
				return func(int) (int, error) {
					i++
					if i < 2 {
						return 42, nil
					}
					return 42, fmt.Errorf("")
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 44,
			ExpectError:      true,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		err := m.Map(tc.MakeMap())

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, FromGo(expectedMap), m, name)
		}

		assert.Equal(t, tc.ExpectedSize, m.Size(), name)

		actualSum := 0
		for _, v := range m.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}

func TestMapNoError(t *testing.T) {
	type TestCase struct {
		InitialMap map[string]int
		MakeMap    func() func(int) int
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
			MakeMap: func() func(int) int {
				return func(i int) int {
					return 42
				}
			},
			ExpectedMap: optionals.Some(map[string]int{}),
		},
		"non-empty map, 42": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeMap: func() func(int) int {
				return func(i int) int {
					return 42
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 42, "bar": 42, "baz": 42,
			}),
		},
		"non-empty map, add 2": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			MakeMap: func() func(int) int {
				return func(i int) int {
					return i + 2
				}
			},
			ExpectedMap: optionals.Some(map[string]int{
				"foo": 3, "bar": 4, "baz": 5,
			}),
		},
		"non-empty map, index": {
			InitialMap: map[string]int{"foo": 0, "bar": 0, "baz": 0},
			MakeMap: func() func(int) int {
				i := 0
				return func(int) int {
					i++
					return i
				}
			},
			ExpectedSize:     3,
			ExpectedValueSum: 6,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		m.MapNoError(tc.MakeMap())

		if expectedMap, exists := tc.ExpectedMap.Get(); exists {
			tc.ExpectedSize = len(expectedMap)

			tc.ExpectedValueSum = 0
			for _, v := range expectedMap {
				tc.ExpectedValueSum += v
			}

			assert.Equal(t, FromGo(expectedMap), m, name)
		}

		assert.Equal(t, tc.ExpectedSize, m.Size(), name)

		actualSum := 0
		for _, v := range m.Entries() {
			actualSum += v
		}
		assert.Equal(t, tc.ExpectedValueSum, actualSum, name)
	}
}

func TestPut(t *testing.T) {
	type TestCase struct {
		InitialMap     map[string]int
		Key            string
		Value          int
		ExpectedMap    map[string]int
		ExpectedResult optionals.Optional[int]
	}
	testCases := map[string]TestCase{
		"empty map": {
			InitialMap:     nil,
			Key:            "foo",
			Value:          42,
			ExpectedMap:    map[string]int{"foo": 42},
			ExpectedResult: optionals.None[int](),
		},
		"non-empty map, new entry": {
			InitialMap:     map[string]int{"foo": 13, "bar": 37},
			Key:            "baz",
			Value:          42,
			ExpectedMap:    map[string]int{"foo": 13, "bar": 37, "baz": 42},
			ExpectedResult: optionals.None[int](),
		},
		"non-empty set, update entry": {
			InitialMap:     map[string]int{"foo": 13, "bar": 37, "baz": 54},
			Key:            "baz",
			Value:          42,
			ExpectedMap:    map[string]int{"foo": 13, "bar": 37, "baz": 42},
			ExpectedResult: optionals.Some(54),
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		actual := m.Put(tc.Key, tc.Value)

		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
		assert.Equal(t, tc.ExpectedResult, actual, name)
	}
}

func TestPutIfAbsent(t *testing.T) {
	type TestCase struct {
		InitialMap     map[string]int
		Key            string
		Value          int
		ExpectedMap    map[string]int
		ExpectedResult optionals.Optional[int]
	}
	testCases := map[string]TestCase{
		"empty map": {
			InitialMap:     nil,
			Key:            "foo",
			Value:          42,
			ExpectedMap:    map[string]int{"foo": 42},
			ExpectedResult: optionals.None[int](),
		},
		"non-empty map, new entry": {
			InitialMap:     map[string]int{"foo": 13, "bar": 37},
			Key:            "baz",
			Value:          42,
			ExpectedMap:    map[string]int{"foo": 13, "bar": 37, "baz": 42},
			ExpectedResult: optionals.None[int](),
		},
		"non-empty set, existing entry": {
			InitialMap:     map[string]int{"foo": 13, "bar": 37, "baz": 54},
			Key:            "baz",
			Value:          42,
			ExpectedMap:    map[string]int{"foo": 13, "bar": 37, "baz": 54},
			ExpectedResult: optionals.Some(54),
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		actual := m.PutIfAbsent(tc.Key, tc.Value)

		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
		assert.Equal(t, tc.ExpectedResult, actual, name)
	}
}

func TestRemove(t *testing.T) {
	type TestCase struct {
		InitialMap     map[string]int
		Key            string
		ExpectedMap    map[string]int
		ExpectedResult optionals.Optional[int]
	}
	testCases := map[string]TestCase{
		"empty map": {
			InitialMap:     nil,
			Key:            "foo",
			ExpectedMap:    nil,
			ExpectedResult: optionals.None[int](),
		},
		"non-empty map, non-existing entry": {
			InitialMap:     map[string]int{"foo": 13, "bar": 37},
			Key:            "baz",
			ExpectedMap:    map[string]int{"foo": 13, "bar": 37},
			ExpectedResult: optionals.None[int](),
		},
		"non-empty set, existing entry": {
			InitialMap:     map[string]int{"foo": 13, "bar": 37, "baz": 54},
			Key:            "baz",
			ExpectedMap:    map[string]int{"foo": 13, "bar": 37},
			ExpectedResult: optionals.Some(54),
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		actual := m.Remove(tc.Key)

		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
		assert.Equal(t, tc.ExpectedResult, actual, name)
	}
}

func TestUpdate(t *testing.T) {
	type TestCase struct {
		InitialMap     map[string]int
		Key            string
		Func           func(optionals.Optional[int]) (int, error)
		ExpectedMap    map[string]int
		ExpectedReturn int
		ExpectError    bool
	}
	testCases := map[string]TestCase{
		"empty map, non-member, no error": {
			InitialMap: nil,
			Key:        "foo",
			Func: func(vOpt optionals.Optional[int]) (int, error) {
				assert.True(t, vOpt.IsNone())
				return 42, nil
			},
			ExpectedMap:    map[string]int{"foo": 42},
			ExpectedReturn: 42,
			ExpectError:    false,
		},
		"empty map, non-member, error": {
			InitialMap: nil,
			Key:        "foo",
			Func: func(vOpt optionals.Optional[int]) (int, error) {
				assert.True(t, vOpt.IsNone())
				return 42, fmt.Errorf("")
			},
			ExpectedMap:    nil,
			ExpectedReturn: 42,
			ExpectError:    true,
		},
		"non-empty map, non-member, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func(vOpt optionals.Optional[int]) (int, error) {
				assert.True(t, vOpt.IsNone())
				return 42, nil
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 42},
			ExpectedReturn: 42,
			ExpectError:    false,
		},
		"non-empty map, non-member, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func(vOpt optionals.Optional[int]) (int, error) {
				assert.True(t, vOpt.IsNone())
				return 42, fmt.Errorf("")
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2},
			ExpectedReturn: 42,
			ExpectError:    true,
		},
		"non-empty map, member, no error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func(vOpt optionals.Optional[int]) (int, error) {
				assert.Equal(t, optionals.Some(3), vOpt)
				return 42, nil
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 42},
			ExpectedReturn: 42,
			ExpectError:    false,
		},
		"non-empty map, member, error": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func(vOpt optionals.Optional[int]) (int, error) {
				assert.Equal(t, optionals.Some(3), vOpt)
				return 42, fmt.Errorf("")
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 3},
			ExpectedReturn: 42,
			ExpectError:    true,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		actual, err := m.Update(tc.Key, tc.Func)

		if tc.ExpectError {
			assert.Error(t, err, name)
		} else {
			assert.NoError(t, err, name)
		}

		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
		assert.Equal(t, tc.ExpectedReturn, actual, name)
	}
}

func TestUpdateNoError(t *testing.T) {
	type TestCase struct {
		InitialMap     map[string]int
		Key            string
		Func           func(optionals.Optional[int]) int
		ExpectedMap    map[string]int
		ExpectedReturn int
	}
	testCases := map[string]TestCase{
		"empty map, non-member": {
			InitialMap: nil,
			Key:        "foo",
			Func: func(vOpt optionals.Optional[int]) int {
				assert.True(t, vOpt.IsNone())
				return 42
			},
			ExpectedMap:    map[string]int{"foo": 42},
			ExpectedReturn: 42,
		},
		"non-empty map, non-member": {
			InitialMap: map[string]int{"foo": 1, "bar": 2},
			Key:        "baz",
			Func: func(vOpt optionals.Optional[int]) int {
				assert.True(t, vOpt.IsNone())
				return 42
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 42},
			ExpectedReturn: 42,
		},
		"non-empty map, member": {
			InitialMap: map[string]int{"foo": 1, "bar": 2, "baz": 3},
			Key:        "baz",
			Func: func(vOpt optionals.Optional[int]) int {
				assert.Equal(t, optionals.Some(3), vOpt)
				return 42
			},
			ExpectedMap:    map[string]int{"foo": 1, "bar": 2, "baz": 42},
			ExpectedReturn: 42,
		},
	}

	for name, tc := range testCases {
		m := NewHashMap[string, int]()
		for k, v := range tc.InitialMap {
			m.Put(k, v)
		}

		actual := m.UpdateNoError(tc.Key, tc.Func)

		assert.Equal(t, FromGo(tc.ExpectedMap), m, name)
		assert.Equal(t, tc.ExpectedReturn, actual, name)
	}
}

func TestValues(t *testing.T) {
	m := NewHashMap[string, int]()
	assert.Equal(t, []int{}, m.Values())

	m.Put("foo", 42)
	m.Put("bar", 37)
	m.Put("baz", 1337)
	m.Put("bar", 42)
	actual := m.Values()
	slices.Sort(actual)
	assert.Equal(t, []int{42, 42, 1337}, actual)
}

func TestJSON(t *testing.T) {
	// Test that a raw map and a HashMap serialize to the same thing.
	m := NewHashMap[string, int]()
	m.Put("foo", 1)
	m.Put("bar", 2)
	m.Put("baz", 3)

	mapJSON, err := json.Marshal(m)
	assert.NoError(t, err)

	rawJSON, err := json.Marshal(m.m)
	assert.NoError(t, err)

	assert.Equal(t, mapJSON, rawJSON)

	// Round-trip test: unmarshal(marshal(m)) == m.
	var deserialized HashMap[string, int]
	err = json.Unmarshal(mapJSON, &deserialized)
	assert.NoError(t, err)
	assert.Equal(t, m, deserialized)
}
