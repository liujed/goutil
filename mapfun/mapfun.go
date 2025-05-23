package mapfun

import (
	"github.com/liujed/goutil/maps"
	"github.com/liujed/goutil/optionals"
)

// Returns a new map containing all entries in the given map that satisfy f.
// All other entries are omitted.
//
// If f returns an error, then that error is returned with the current filtered
// map after applying the filter to the current map entry. Map entries are
// processed in the same order as they appear during iteration via
// [maps.UnmodifiableMap.Entries].
//
// This is the functional version of [maps.Map.Filter].
func Filter[K comparable, V any](
	m maps.UnmodifiableMap[K, V],
	f func(K, V) (bool, error),
) (maps.Map[K, V], error) {
	result := maps.NewEmpty[K, V, K, V](m)
	for k, v := range m.Entries() {
		keep, err := f(k, v)
		if keep {
			result.Put(k, v)
		}
		if err != nil {
			return result, err
		}
	}
	return result, nil
}

// Like [Filter], but without support for errors.
//
// This is the functional version of [maps.Map.FilterNoError].
func FilterNoError[K comparable, V any](
	m maps.UnmodifiableMap[K, V],
	f func(K, V) bool,
) maps.Map[K, V] {
	result, _ := Filter(
		m,
		func(k K, v V) (bool, error) {
			return f(k, v), nil
		},
	)
	return result
}

// Returns a new map containing all entries in the given map whose key satisfies
// f. All other entries are omitted.
//
// If f returns an error, then that error is returned with the current filtered
// map after applying the filter to the current map key. Map entries are
// processed in the same order as they appear during iteration via
// [maps.UnmodifiableMap.Entries].
//
// This is the functional version of [maps.Map.FilterKeys].
func FilterKeys[K comparable, V any](
	m maps.UnmodifiableMap[K, V],
	f func(K) (bool, error),
) (maps.Map[K, V], error) {
	return Filter(
		m,
		func(k K, v V) (bool, error) {
			return f(k)
		},
	)
}

// Like [FilterKeys], but without support for errors.
//
// This is the functional version of [maps.Map.FilterKeysNoError].
func FilterKeysNoError[K comparable, V any](
	m maps.UnmodifiableMap[K, V],
	f func(K) bool,
) maps.Map[K, V] {
	result, _ := Filter(
		m,
		func(k K, v V) (bool, error) {
			return f(k), nil
		},
	)
	return result
}

// Returns a new map containing all entries in the given map whose value
// satisfies f. All other entries are omitted.
//
// If f returns an error, then that error is returned with the current filtered
// map after applying the filter to the current map value. Map entries are
// processed in the same order as they appear during iteration via
// [maps.UnmodifiableMap.Entries].
//
// This is the functional version of [maps.Map.FilterValues].
func FilterValues[K comparable, V any](
	m maps.UnmodifiableMap[K, V],
	f func(V) (bool, error),
) (maps.Map[K, V], error) {
	return Filter(
		m,
		func(k K, v V) (bool, error) {
			return f(v)
		},
	)
}

// Like [FilterValues], but without support for errors.
//
// This is the functional version of [maps.Map.FilterValuesNoError].
func FilterValuesNoError[K comparable, V any](
	m maps.UnmodifiableMap[K, V],
	f func(V) bool,
) maps.Map[K, V] {
	result, _ := Filter(
		m,
		func(k K, v V) (bool, error) {
			return f(v), nil
		},
	)
	return result
}

// Returns a new map with each value replaced by f applied to the entry of that
// value. If f returns None, then that entry is omitted.
//
// If f returns an error, then that error is returned with the partial map
// constructed thus far, after applying the filter-map to the current entry.
// Map entries are processed in the same order as they appear during iteration
// via [maps.UnmodifiableMap.Entries].
//
// This is the functional version of [maps.Map.FilterMap].
func FilterMap[K comparable, V1 any, V2 any](
	m maps.UnmodifiableMap[K, V1],
	f func(K, V1) (optionals.Optional[V2], error),
) (maps.Map[K, V2], error) {
	result := maps.NewEmpty[K, V1, K, V2](m)
	for k, v := range m.Entries() {
		vOpt, err := f(k, v)
		if v, exists := vOpt.Get(); exists {
			result.Put(k, v)
		}
		if err != nil {
			return result, err
		}
	}
	return result, nil
}

// Like [FilterMap], but without support for errors.
//
// This is the functional version of [maps.Map.FilterMapNoError].
func FilterMapNoError[K comparable, V1 any, V2 any](
	m maps.UnmodifiableMap[K, V1],
	f func(K, V1) optionals.Optional[V2],
) maps.Map[K, V2] {
	result, _ := FilterMap(
		m,
		func(k K, v V1) (optionals.Optional[V2], error) {
			return f(k, v), nil
		},
	)
	return result
}

// Returns a new map with each value replaced by f applied to that value. If f
// returns None, then that value's entry is omitted.
//
// If f returns an error, then that error is returned with the partial map
// constructed thus far, after applying the filter-map to the current value. Map
// entries are processed in the same order as they appear during iteration via
// [maps.UnmodifiableMap.Entries].
//
// This is the functional version of [maps.Map.FilterMapValues].
func FilterMapValues[K comparable, V1 any, V2 any](
	m maps.UnmodifiableMap[K, V1],
	f func(V1) (optionals.Optional[V2], error),
) (maps.Map[K, V2], error) {
	return FilterMap(
		m,
		func(k K, v V1) (optionals.Optional[V2], error) {
			return f(v)
		},
	)
}

// Like [FilterMapValues], but without support for errors.
//
// This is the functional version of [maps.Map.FilterMapValuesNoError].
func FilterMapValuesNoError[K comparable, V1 any, V2 any](
	m maps.UnmodifiableMap[K, V1],
	f func(V1) optionals.Optional[V2],
) maps.Map[K, V2] {
	result, _ := FilterMap(
		m,
		func(k K, v V1) (optionals.Optional[V2], error) {
			return f(v), nil
		},
	)
	return result
}

// Folds over the keys and values in the given map. Map entries are processed in
// the same order as they appear during iteration via
// [maps.UnmodifiableMap.Entries].
//
// If f returns an error, then iteration stops and that error is returned with
// the current accumulated value.
func Fold[K comparable, V any, T any](
	m maps.UnmodifiableMap[K, V],
	init T,
	f func(k K, v V, accum T) (T, error),
) (T, error) {
	result := init
	for k, v := range m.Entries() {
		var err error
		result, err = f(k, v, result)
		if err != nil {
			return result, err
		}
	}
	return result, nil
}

// Like [Fold], but without support for errors.
func FoldNoError[K comparable, V any, T any](
	m maps.UnmodifiableMap[K, V],
	init T,
	f func(k K, v V, accum T) T,
) T {
	result, _ := Fold(
		m,
		init,
		func(k K, v V, accum T) (T, error) {
			return f(k, v, accum), nil
		},
	)
	return result
}

// Returns a new map with each value replaced by f applied to that value. If f
// returns an error, then that error is returned with the partial map
// constructed thus far, excluding the entry that caused the error. Map entries
// are processed in the same order as they appear during iteration via
// [maps.UnmodifiableMap.Entries].
//
// This is the functional version of [maps.Map.Map].
func Map[K comparable, V1 any, V2 any](
	m maps.UnmodifiableMap[K, V1],
	f func(V1) (V2, error),
) (maps.Map[K, V2], error) {
	result := maps.NewEmpty[K, V1, K, V2](m)
	for k, v := range m.Entries() {
		v, err := f(v)
		if err != nil {
			return result, err
		}
		result.Put(k, v)
	}
	return result, nil
}

// Like [Map], but without support for errors.
//
// This is the functional version of [maps.Map.MapNoError].
func MapNoError[K comparable, V1 any, V2 any](
	m maps.UnmodifiableMap[K, V1],
	f func(V1) V2,
) maps.Map[K, V2] {
	result, _ := Map(
		m,
		func(v V1) (V2, error) {
			return f(v), nil
		},
	)
	return result
}
