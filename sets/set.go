package sets

type Set[T comparable] interface {
	UnmodifiableSet[T]

	// Adds the given element to this set. Returns true if the element was not
	// already a member; false otherwise.
	Add(T) bool

	// Clears all elements from this set.
	Clear()

	// Retains in this set all elements that satisfy f. All other elements are
	// removed.
	//
	// If f returns an error, then iteration stops and that error is returned.
	// Filtering is NOT applied to the element that causes the error. Set elements
	// are processed in the same order as they appear during iteration via
	// [UnmodifiableSet.Elements].
	//
	// This is the imperative version of [setfun.Filter].
	Filter(f func(T) (bool, error)) error

	// Like [Filter], but without support for errors.
	//
	// This is the imperative version of [setfun.FilterNoError].
	FilterNoError(f func(T) bool)

	// Removes the given element from this set. This is a no-op if the element is
	// not a member of this set.
	Remove(T)
}

// Returns a new set having the same underlying implementation as the one given.
func NewEmpty[T1 comparable, T2 comparable](s UnmodifiableSet[T1]) Set[T2] {
	return NewHashSet[T2]()
}
