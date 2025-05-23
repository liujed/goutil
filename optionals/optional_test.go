package optionals

import (
	"encoding/json"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestIsSome(t *testing.T) {
	some := Some("foo")
	none := None[string]()
	assert.True(t, some.IsSome())
	assert.False(t, none.IsSome())
}

func TestIsNone(t *testing.T) {
	some := Some("foo")
	none := None[string]()
	assert.True(t, none.IsNone())
	assert.False(t, some.IsNone())
}

func TestGet(t *testing.T) {
	some := Some("foo")
	none := None[string]()

	s, exists := some.Get()
	assert.True(t, exists)
	assert.Equal(t, "foo", s)

	_, exists = none.Get()
	assert.False(t, exists)
}

func TestGetOrDefault(t *testing.T) {
	some := Some("foo")
	none := None[string]()

	s := some.GetOrDefault("bar")
	assert.Equal(t, "foo", s)

	s = none.GetOrDefault("bar")
	assert.Equal(t, "bar", s)
}

func TestSomeJSON(t *testing.T) {
	// Test that Some("foo") and "foo" serialize to the same thing.
	some := Some("foo")

	someJSON, err := json.Marshal(some)
	assert.NoError(t, err)

	rawJSON, err := json.Marshal(some.value)
	assert.NoError(t, err)

	assert.Equal(t, someJSON, rawJSON)

	// Round-trip test: unmarshal(marshal(some)) == some.
	var deserialized Optional[string]
	err = json.Unmarshal(someJSON, &deserialized)
	assert.NoError(t, err)
	assert.Equal(t, some, deserialized)
}

func TestNoneJSON(t *testing.T) {
	// Test that nil and None serialize to the same thing.
	none := None[string]()

	noneJSON, err := json.Marshal(none)
	assert.NoError(t, err)

	rawJSON, err := json.Marshal(none.value)
	assert.NoError(t, err)

	assert.Equal(t, noneJSON, rawJSON)

	// Round-trip test: unmarshal(marshal(none)) == none.
	var deserialized Optional[string]
	err = json.Unmarshal(noneJSON, &deserialized)
	assert.NoError(t, err)
	assert.Equal(t, none, deserialized)
}
