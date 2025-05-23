package sets

import (
	"iter"

	"github.com/liujed/goutil/optionals"
)

type UnmodifiableSet[T comparable] interface {
	// Returns an arbitrary element of this set, or None if empty.
	Choose() optionals.Optional[T]

	// Determines whether the given element is a member of this set.
	Contains(T) bool

	// Determines the number of elements in this set that satisfy f.
	//
	// If f returns an error, then iteration stops and that error is returned with
	// the count obtained thus far. If true is returned alongside the error, then
	// this is included in the returned count. Set elements are processed in the
	// same order as they appear during iteration via [Elements].
	Count(f func(T) (bool, error)) (int, error)

	// Like [Count], but without support for errors.
	CountNoError(func(T) bool) int

	// Returns an interator over the elements in this set.
	Elements() iter.Seq[T]

	// Returns true if any element of this set satisfies f.
	//
	// If f returns an error, then iteration stops and that error is returned. Set
	// elements are processed in the same order as they appear during iteration
	// via [Elements].
	Exists(f func(T) (bool, error)) (bool, error)

	// Like [Exists], but without support for errors.
	ExistsNoError(func(T) bool) bool

	// Returns an element of this set that satisfies f.
	//
	// If f returns an error, then iteration stops and that error is returned. Set
	// elements are processed in the same order as they appear during iteration
	// via [Elements].
	Find(func(T) (bool, error)) (optionals.Optional[T], error)

	// Like [Find], but without support for errors.
	FindNoError(func(T) bool) optionals.Optional[T]

	// Returns true if all elements of this set satisfy f.
	//
	// If f returns an error, then iteration stops and that error is returned. Set
	// elements are processed in the same order as they appear during iteration
	// via [Elements].
	ForAll(f func(T) (bool, error)) (bool, error)

	// Like [ForAll], but without support for errors.
	ForAllNoError(func(T) bool) bool

	// Determines whether this set is empty.
	IsEmpty() bool

	// Returns the number of elements in this set.
	Size() int

	// Returns a slice containing all of the elements in this set.
	ToSlice() []T
}
