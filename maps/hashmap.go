package maps

import (
	"encoding/json"
	"iter"

	"github.com/liujed/goutil/optionals"
	"github.com/liujed/goutil/sets"
)

type HashMap[K comparable, V any] struct {
	m map[K]V
}

var _ Map[any, any] = (*HashMap[any, any])(nil)
var _ json.Marshaler = (*HashMap[any, any])(nil)
var _ json.Unmarshaler = (*HashMap[any, any])(nil)

func NewHashMap[K comparable, V any]() HashMap[K, V] {
	return HashMap[K, V]{
		m: map[K]V{},
	}
}

func (m HashMap[K, V]) Change(
	k K,
	f func(optionals.Optional[V]) (optionals.Optional[V], error),
) (optionals.Optional[V], error) {
	result, err := f(m.Get(k))
	if err == nil {
		if newValue, exists := result.Get(); exists {
			m.m[k] = newValue
		} else {
			delete(m.m, k)
		}
	}
	return result, err
}

func (m HashMap[K, V]) ChangeNoError(
	k K,
	f func(optionals.Optional[V]) optionals.Optional[V],
) optionals.Optional[V] {
	result, _ := m.Change(
		k,
		func(v optionals.Optional[V]) (optionals.Optional[V], error) {
			return f(v), nil
		},
	)
	return result
}

func (m HashMap[K, V]) Clear() {
	clear(m.m)
}

func (m HashMap[K, V]) ComputeIfAbsent(k K, f func() (V, error)) (V, error) {
	if v, exists := m.Get(k).Get(); exists {
		return v, nil
	}

	v, err := f()
	if err == nil {
		m.Put(k, v)
	}
	return v, err
}

func (m HashMap[K, V]) ComputeIfAbsentNoError(k K, f func() V) V {
	if v, exists := m.Get(k).Get(); exists {
		return v
	}

	v := f()
	m.Put(k, v)
	return v
}

func (m HashMap[K, V]) ContainsKey(k K) bool {
	_, exists := m.m[k]
	return exists
}

func (m HashMap[K, V]) Entries() iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for k, v := range m.m {
			if !yield(k, v) {
				return
			}
		}
	}
}

func (m HashMap[K, V]) Filter(f func(K, V) (bool, error)) error {
	for k, v := range m.Entries() {
		keep, err := f(k, v)
		if err != nil {
			return err
		}
		if !keep {
			delete(m.m, k)
		}
	}
	return nil
}

func (m HashMap[K, V]) FilterNoError(f func(K, V) bool) {
	m.Filter(
		func(k K, v V) (bool, error) {
			return f(k, v), nil
		},
	)
}

func (m HashMap[K, V]) FilterKeys(f func(K) (bool, error)) error {
	return m.Filter(
		func(k K, v V) (bool, error) {
			return f(k)
		},
	)
}

func (m HashMap[K, V]) FilterKeysNoError(f func(K) bool) {
	m.Filter(
		func(k K, v V) (bool, error) {
			return f(k), nil
		},
	)
}

func (m HashMap[K, V]) FilterValues(f func(V) (bool, error)) error {
	return m.Filter(
		func(k K, v V) (bool, error) {
			return f(v)
		},
	)
}

func (m HashMap[K, V]) FilterValuesNoError(f func(V) bool) {
	m.Filter(
		func(k K, v V) (bool, error) {
			return f(v), nil
		},
	)
}

func (m HashMap[K, V]) FilterMap(
	f func(K, V) (optionals.Optional[V], error),
) error {
	for k, v := range m.Entries() {
		vOpt, err := f(k, v)
		if err != nil {
			return err
		}
		if v, keep := vOpt.Get(); keep {
			m.m[k] = v
		} else {
			delete(m.m, k)
		}
	}
	return nil
}

func (m HashMap[K, V]) FilterMapNoError(
	f func(K, V) optionals.Optional[V],
) {
	m.FilterMap(
		func(k K, v V) (optionals.Optional[V], error) {
			return f(k, v), nil
		},
	)
}

func (m HashMap[K, V]) FilterMapValues(
	f func(V) (optionals.Optional[V], error),
) error {
	return m.FilterMap(
		func(k K, v V) (optionals.Optional[V], error) {
			return f(v)
		},
	)
}

func (m HashMap[K, V]) FilterMapValuesNoError(
	f func(V) optionals.Optional[V],
) {
	m.FilterMap(
		func(k K, v V) (optionals.Optional[V], error) {
			return f(v), nil
		},
	)
}

func (m HashMap[K, V]) Get(k K) optionals.Optional[V] {
	if v, exists := m.m[k]; exists {
		return optionals.Some(v)
	}

	return optionals.None[V]()
}

func (m HashMap[K, V]) IsEmpty() bool {
	return len(m.m) == 0
}

func (m HashMap[K, V]) KeySet() sets.Set[K] {
	result := sets.NewHashSet[K]()
	for k := range m.m {
		result.Add(k)
	}
	return result
}

func (m HashMap[K, V]) Map(f func(V) (V, error)) error {
	for k, v := range m.Entries() {
		v, err := f(v)
		if err != nil {
			return err
		}
		m.m[k] = v
	}
	return nil
}

func (m HashMap[K, V]) MapNoError(f func(V) V) {
	m.Map(
		func(v V) (V, error) {
			return f(v), nil
		},
	)
}

func (m HashMap[K, V]) Put(k K, v V) optionals.Optional[V] {
	result := m.Get(k)
	m.m[k] = v
	return result
}

func (m HashMap[K, V]) PutIfAbsent(k K, v V) optionals.Optional[V] {
	result := m.Get(k)
	if result.IsNone() {
		m.Put(k, v)
	}
	return result
}

func (m HashMap[K, V]) Remove(k K) optionals.Optional[V] {
	result := m.Get(k)
	delete(m.m, k)
	return result
}

func (m HashMap[K, V]) Size() int {
	return len(m.m)
}

func (m HashMap[K, V]) Update(
	k K,
	f func(optionals.Optional[V]) (V, error),
) (V, error) {
	resultOpt, err := m.Change(
		k,
		func(o optionals.Optional[V]) (optionals.Optional[V], error) {
			newV, err := f(o)
			return optionals.Some(newV), err
		},
	)

	result, _ := resultOpt.Get()
	return result, err
}

func (m HashMap[K, V]) UpdateNoError(
	k K,
	f func(optionals.Optional[V]) V,
) V {
	resultOpt, _ := m.Change(
		k,
		func(o optionals.Optional[V]) (optionals.Optional[V], error) {
			newV := f(o)
			return optionals.Some(newV), nil
		},
	)

	result, _ := resultOpt.Get()
	return result
}

func (m HashMap[K, V]) Values() []V {
	result := make([]V, 0, len(m.m))
	for _, v := range m.m {
		result = append(result, v)
	}
	return result
}

// Creates a HashMap from a Go map. Modifications to the returned map will be
// reflected in the Go map, and vice versa.
//
// Returns an empty HashMap if the given map is nil.
func FromGo[K comparable, V any](m map[K]V) HashMap[K, V] {
	if m == nil {
		m = map[K]V{}
	}
	return HashMap[K, V]{
		m: m,
	}
}

func (m HashMap[K, V]) ToGo() map[K]V {
	return m.m
}

func (m HashMap[K, V]) MarshalJSON() ([]byte, error) {
	return json.Marshal(m.m)
}

func (m *HashMap[K, V]) UnmarshalJSON(data []byte) error {
	return json.Unmarshal(data, &m.m)
}
