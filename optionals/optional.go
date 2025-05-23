package optionals

import "encoding/json"

type Optional[T any] struct {
	value *T
}

var _ json.Marshaler = (*Optional[any])(nil)
var _ json.Unmarshaler = (*Optional[any])(nil)

func Some[T any](v T) Optional[T] {
	return Optional[T]{
		value: &v,
	}
}

func None[T any]() Optional[T] {
	return Optional[T]{
		value: nil,
	}
}

func (opt Optional[T]) IsSome() bool {
	return opt.value != nil
}

func (opt Optional[T]) IsNone() bool {
	return opt.value == nil
}

// If this Optional is Some, returns the value inhabiting this Optional and
// true. Otherwise, returns the Go's default value for T and false.
func (opt Optional[T]) Get() (T, bool) {
	if opt.IsNone() {
		var emptyT T
		return emptyT, false
	}

	return *opt.value, true
}

// Returns the value inhabiting this Optional, or the given default value if
// this Optional is None.
func (opt Optional[T]) GetOrDefault(defaultValue T) T {
	v, exists := opt.Get()
	if !exists {
		return defaultValue
	}
	return v
}

func (opt Optional[T]) MarshalJSON() ([]byte, error) {
	return json.Marshal(opt.value)
}

func (opt *Optional[T]) UnmarshalJSON(data []byte) error {
	return json.Unmarshal(data, &opt.value)
}
