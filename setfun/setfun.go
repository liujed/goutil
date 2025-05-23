package setfun

import (
	"github.com/liujed/goutil/optionals"
	"github.com/liujed/goutil/sets"
)

// Returns a new set containing all elements in the given set that satisfy f.
// All other elements are omitted.
//
// If f returns an error, then iteration stops and that error is returned after
// applying the filter to the current element. Set elements are processed in the
// same order as they appear during iteration via [UnmodifiableSet.Elements].
//
// This is the functional version of [sets.Set.Filter].
func Filter[T comparable](
	s sets.UnmodifiableSet[T],
	f func(T) (bool, error),
) (sets.Set[T], error) {
	result := sets.NewEmpty[T, T](s)
	for elt := range s.Elements() {
		keep, err := f(elt)
		if keep {
			result.Add(elt)
		}
		if err != nil {
			return result, err
		}
	}
	return result, nil
}

// Like [Filter], but without support for errors.
//
// This is the functional version of [sets.Set.FilterNoError].
func FilterNoError[T comparable](
	s sets.UnmodifiableSet[T],
	f func(T) bool,
) sets.Set[T] {
	result, _ := Filter(
		s,
		func(t T) (bool, error) {
			return f(t), nil
		},
	)
	return result
}

// Returns a new set created by applying f to every element in the given set. If
// f returns None, then that element is omitted.
//
// If f returns an error, then that error is returned with the partial set
// constructed thus far, after applying the filter-map to the current entry.
// Set elements are processed in the same order as they appear during iteration
// via [sets.UnmodifiableSet.Elements].
func FilterMap[T1 comparable, T2 comparable](
	s sets.UnmodifiableSet[T1],
	f func(T1) (optionals.Optional[T2], error),
) (sets.Set[T2], error) {
	result := sets.NewEmpty[T1, T2](s)
	for elt := range s.Elements() {
		eltOpt, err := f(elt)
		if elt, exists := eltOpt.Get(); exists {
			result.Add(elt)
		}
		if err != nil {
			return result, err
		}
	}
	return result, nil
}

// Like [FilterMap], but without support for errors.
func FilterMapNoError[T1 comparable, T2 comparable](
	s sets.UnmodifiableSet[T1],
	f func(T1) optionals.Optional[T2],
) sets.Set[T2] {
	result, _ := FilterMap(
		s,
		func(elt T1) (optionals.Optional[T2], error) {
			return f(elt), nil
		},
	)
	return result
}

// Folds over the elements in the given set. Set elements are processed in the
// same order as they appear during iteration via
// [sets.UnmodifiableSet.Elements].
//
// If f returns an error, then iteration stops and that error is returned with
// the current accumulated value.
func Fold[T comparable, V any](
	s sets.UnmodifiableSet[T],
	init V,
	f func(elt T, accum V) (V, error),
) (V, error) {
	result := init
	for elt := range s.Elements() {
		var err error
		result, err = f(elt, result)
		if err != nil {
			return result, err
		}
	}
	return result, nil
}

// Like [Fold], but without support for errors.
func FoldNoError[T comparable, V any](
	s sets.UnmodifiableSet[T],
	init V,
	f func(elt T, accum V) V,
) V {
	result, _ := Fold(
		s,
		init,
		func(elt T, accum V) (V, error) {
			return f(elt, accum), nil
		},
	)
	return result
}

// Returns a new set created by applying f to every element in the given set. If
// f returns an error, then that error is returned with the partial set
// constructed thus far, excluding the element that caused the error. Set
// elements are processed in the same order as they appear during iteration via
// [sets.UnmodifiableSet.Elements].
func Map[T1 comparable, T2 comparable](
	s sets.UnmodifiableSet[T1],
	f func(T1) (T2, error),
) (sets.Set[T2], error) {
	result := sets.NewEmpty[T1, T2](s)
	for elt := range s.Elements() {
		elt, err := f(elt)
		if err != nil {
			return result, err
		}
		result.Add(elt)
	}
	return result, nil
}

// Like [Map], but without support for errors.
func MapNoError[T1 comparable, T2 comparable](
	s sets.UnmodifiableSet[T1],
	f func(T1) T2,
) sets.Set[T2] {
	result, _ := Map(
		s,
		func(t T1) (T2, error) {
			return f(t), nil
		},
	)
	return result
}
