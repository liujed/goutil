package maps

import (
	"iter"

	"github.com/liujed/goutil/optionals"
	"github.com/liujed/goutil/sets"
)

type UnmodifiableMap[K comparable, V any] interface {
	// Determines whether this map has an entry for the given key.
	ContainsKey(K) bool

	// Returns an iterator over the entries in this map. The order of iteration is
	// implementation-dependent.
	Entries() iter.Seq2[K, V]

	// Returns the value associated with the given key in this map, if any.
	Get(K) optionals.Optional[V]

	// Determines whether this map is empty.
	IsEmpty() bool

	// Returns the set of keys in this map.
	KeySet() sets.Set[K]

	// Returns the number of entries in this map.
	Size() int

	// Returns the values in this map.
	Values() []V
}
