package maps

import (
	"github.com/liujed/goutil/optionals"
)

type Map[K comparable, V any] interface {
	UnmodifiableMap[K, V]

	// Calls f with the current value associated with the given key in this map.
	// The map is then modified to associate the key with the result of f. If f
	// returns None, then the key is removed from the map. The map is not modified
	// if f returns an error.
	//
	// Returns the result of calling f.
	Change(
		key K,
		f func(optionals.Optional[V]) (optionals.Optional[V], error),
	) (optionals.Optional[V], error)

	// Like [Change], but without support for errors.
	ChangeNoError(
		key K,
		f func(optionals.Optional[V]) optionals.Optional[V],
	) optionals.Optional[V]

	// Removes all entries from this map.
	Clear()

	// If the given key is not already associated with a value in this map, then
	// it is associated with the result of calling f.
	//
	// If f returns an error, then this map is not modified, and the result of the
	// call to f, including the error, is returned. Otherwise, returns the
	// resulting value associated with the given key.
	ComputeIfAbsent(k K, f func() (V, error)) (V, error)

	// Like [ComputeIfAbsent], but without support for errors.
	ComputeIfAbsentNoError(K, func() V) V

	// Retains in this map all entries that satisfy f. All other entries are
	// removed.
	//
	// If f returns an error, then iteration stops and that error is returned.
	// Filtering is NOT applied to the entry that causes the error. Map entries
	// are processed in the same order as they appear during iteration via
	// [UnmodifiableMap.Entries].
	//
	// This is the imperative version of [mapfun.Filter].
	Filter(f func(K, V) (bool, error)) error

	// Like [Filter], but without support for errors.
	//
	// This is the imperative version of [mapfun.FilterNoError].
	FilterNoError(f func(K, V) bool)

	// Retains in this map all entries whose key satisfies f. All other entries
	// are removed.
	//
	// If f returns an error, then iteration stops and that error is returned.
	// Filtering is NOT applied to the key that causes the error. Map entries are
	// processed in the same order as they appear during iteration via
	// [UnmodifiableMap.Entries].
	//
	// This is the imperative version of [mapfun.FilterKeys].
	FilterKeys(f func(K) (bool, error)) error

	// Like [FilterKeys], but without support for errors.
	//
	// This is the imperative version of [mapfun.FilterKeysNoError].
	FilterKeysNoError(f func(K) bool)

	// Retains in this map all entries whose value satisfies f. All other entries
	// are removed.
	//
	// If f returns an error, then iteration stops and that error is returned.
	// Filtering is NOT applied to the value that causes the error. Map entries
	// are processed in the same order as they appear during iteration via
	// [UnmodifiableMap.Entries].
	//
	// This is the imperative version of [mapfun.FilterValues].
	FilterValues(f func(V) (bool, error)) error

	// Like [FilterValues], but without support for errors.
	//
	// This is the imperative version of [mapfun.FilterValuesNoError].
	FilterValuesNoError(f func(V) bool)

	// Replaces each value in this map with f applied to the entry of that value.
	// If f returns None, then the entry is removed.
	//
	// If f returns an error, then iteration stops and that error is returned.
	// Filtering is NOT applied to the entry that causes the error.  Map entries
	// are processed in the same order as they appear during iteration via
	// [UnmodifiableMap.Entries].
	//
	// This is the imperative version of [mapfun.FilterMap].
	FilterMap(f func(K, V) (optionals.Optional[V], error)) error

	// Like [FilterMap], but without support for errors.
	//
	// This is the imperative version of [mapfun.FilterMapNoError].
	FilterMapNoError(f func(K, V) optionals.Optional[V])

	// Replaces each value in this map with f applied to that value.  If f returns
	// None, then the value's entry is removed.
	//
	// If f returns an error, then iteration stops and that error is returned.
	// Filtering is NOT applied to the value that causes the error. Map entries
	// are processed in the same order as they appear during iteration via
	// [UnmodifiableMap.Entries].
	//
	// This is the imperative version of [mapfun.FilterMapValues].
	FilterMapValues(f func(V) (optionals.Optional[V], error)) error

	// Like [FilterMapValues], but without support for errors.
	//
	// This is the imperative version of [mapfun.FilterMapValuesNoError].
	FilterMapValuesNoError(f func(V) optionals.Optional[V])

	// Replaces each value in this map with f applied to that value.
	//
	// If f returns an error, then iteration stops and that error is returned; the
	// current value is left unchanged.  Map entries are processed in the same
	// order as they appear during iteration via [UnmodifiableMap.Entries].
	//
	// This is the imperative version of [mapfun.Map].
	Map(f func(V) (V, error)) error

	// Like [Map], but without support for errors.
	//
	// This is the imperative version of [mapfun.MapNoError].
	MapNoError(f func(V) V)

	// Associates the given value with the given key in this map. Returns the
	// previous value associated with the given key, if any.
	Put(K, V) optionals.Optional[V]

	// If the given key is not already associated with a value in this map, then
	// it is associated with the given value and None is returned. Otherwise, the
	// map is left unchanged, and the value associated with the key is returned.
	PutIfAbsent(K, V) optionals.Optional[V]

	// Removes the entry associated with the given key from this map. Returns the
	// value in the removed entry, if any.
	Remove(K) optionals.Optional[V]

	// Calls f with the current value associated with the given key in this map.
	// The map is then modified to associate the key with the result of the
	// f. The map is not modified if f returns an error.
	//
	// Returns the result of calling f.
	Update(
		key K,
		f func(optionals.Optional[V]) (V, error),
	) (V, error)

	// Like [Update], but without support for errors.
	UpdateNoError(
		key K,
		f func(optionals.Optional[V]) V,
	) V

	// Returns the native Go object underpinning this map. Modifications to the
	// returned object will be reflected in this map, and vice versa.
	ToGo() map[K]V
}

// Returns a new map having the same underlying implementation as the one given.
func NewEmpty[K1 comparable, V1 any, K2 comparable, V2 any](
	m UnmodifiableMap[K1, V1],
) Map[K2, V2] {
	return NewHashMap[K2, V2]()
}
