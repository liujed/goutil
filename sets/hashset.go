package sets

import (
	"encoding/json"
	"iter"

	"github.com/liujed/goutil/optionals"
)

type HashSet[T comparable] struct {
	m map[T]struct{}
}

var _ Set[any] = (*HashSet[any])(nil)
var _ json.Marshaler = (*HashSet[any])(nil)
var _ json.Unmarshaler = (*HashSet[any])(nil)

func NewHashSet[T comparable](ts ...T) HashSet[T] {
	result := HashSet[T]{
		m: map[T]struct{}{},
	}

	for _, t := range ts {
		result.Add(t)
	}
	return result
}

func (s HashSet[T]) Add(elt T) bool {
	if s.Contains(elt) {
		return false
	}

	s.m[elt] = struct{}{}
	return true
}

func (s HashSet[T]) Choose() optionals.Optional[T] {
	for elt := range s.Elements() {
		return optionals.Some(elt)
	}
	return optionals.None[T]()
}

func (s HashSet[T]) Clear() {
	clear(s.m)
}

func (s HashSet[T]) Contains(elt T) bool {
	_, exists := s.m[elt]
	return exists
}

func (s HashSet[T]) Count(f func(T) (bool, error)) (int, error) {
	result := 0
	for elt := range s.Elements() {
		sat, err := f(elt)
		if sat {
			result++
		}
		if err != nil {
			return result, err
		}
	}
	return result, nil
}

func (s HashSet[T]) CountNoError(f func(T) bool) int {
	result, _ := s.Count(
		func(t T) (bool, error) {
			return f(t), nil
		},
	)
	return result
}

func (s HashSet[T]) Elements() iter.Seq[T] {
	return func(yield func(T) bool) {
		for e := range s.m {
			if !yield(e) {
				return
			}
		}
	}
}

func (s HashSet[T]) Exists(f func(T) (bool, error)) (bool, error) {
	for elt := range s.Elements() {
		sat, err := f(elt)
		if sat || err != nil {
			return sat, err
		}
	}
	return false, nil
}

func (s HashSet[T]) ExistsNoError(f func(T) bool) bool {
	result, _ := s.Exists(
		func(t T) (bool, error) {
			return f(t), nil
		},
	)
	return result
}

func (s HashSet[T]) Filter(f func(T) (bool, error)) error {
	for elt := range s.Elements() {
		sat, err := f(elt)
		if err != nil {
			return err
		}
		if !sat {
			s.Remove(elt)
		}
	}
	return nil
}

func (s HashSet[T]) FilterNoError(f func(T) bool) {
	s.Filter(
		func(t T) (bool, error) {
			return f(t), nil
		},
	)
}

func (s HashSet[T]) Find(
	f func(T) (bool, error),
) (optionals.Optional[T], error) {
	for elt := range s.Elements() {
		sat, err := f(elt)
		if sat {
			return optionals.Some(elt), err
		}
		if err != nil {
			return optionals.None[T](), err
		}
	}
	return optionals.None[T](), nil
}

func (s HashSet[T]) FindNoError(f func(T) bool) optionals.Optional[T] {
	result, _ := s.Find(
		func(t T) (bool, error) {
			return f(t), nil
		},
	)
	return result
}

func (s HashSet[T]) ForAll(f func(T) (bool, error)) (bool, error) {
	for elt := range s.Elements() {
		sat, err := f(elt)
		if !sat || err != nil {
			return sat, err
		}
	}
	return true, nil
}

func (s HashSet[T]) ForAllNoError(f func(T) bool) bool {
	result, _ := s.ForAll(
		func(t T) (bool, error) {
			return f(t), nil
		},
	)
	return result
}

func (s HashSet[T]) IsEmpty() bool {
	return len(s.m) == 0
}

func (s HashSet[T]) Remove(elt T) {
	delete(s.m, elt)
}

func (s HashSet[T]) Size() int {
	return len(s.m)
}

func (s HashSet[T]) ToSlice() []T {
	result := make([]T, 0, s.Size())
	for e := range s.m {
		result = append(result, e)
	}
	return result
}

func (s HashSet[T]) MarshalJSON() ([]byte, error) {
	return json.Marshal(s.ToSlice())
}

func (s *HashSet[T]) UnmarshalJSON(data []byte) error {
	var slice []T
	err := json.Unmarshal(data, &slice)
	if err != nil {
		return err
	}

	s.m = make(map[T]struct{}, len(slice))
	for _, e := range slice {
		s.m[e] = struct{}{}
	}

	return nil
}
