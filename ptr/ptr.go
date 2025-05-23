package ptr

// Returns a pointer to the given value.
func Of[T any](v T) *T {
	return &v
}
