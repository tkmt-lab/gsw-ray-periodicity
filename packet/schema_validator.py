import re

def validate(value, schema, whole, where='$'):
    """Validate the closed JSON-schema vocabulary used by this file, offline."""
    if '$ref' in schema:
        target = whole
        assert schema['$ref'].startswith('#/')
        for part in schema['$ref'][2:].split('/'):
            target = target[part]
        return validate(value, target, whole, where)
    supported = {'$schema','title','type','required','properties','additionalProperties','items',
                 'minItems','maxItems','minLength','minimum','pattern','const','enum','$defs'}
    assert set(schema) <= supported, ('unsupported schema keyword', where)
    if 'const' in schema:
        assert type(value) is type(schema['const']) and value == schema['const'], where
    if 'enum' in schema:
        assert value in schema['enum'], where
    types = {'object':dict,'array':list,'string':str,'integer':int,'null':type(None),'boolean':bool}
    if 'type' in schema:
        names = schema['type'] if isinstance(schema['type'], list) else [schema['type']]
        assert any(type(value) is types[n] for n in names), where
    if isinstance(value, dict):
        assert set(schema.get('required', [])) <= set(value), where
        props = schema.get('properties', {})
        extra = schema.get('additionalProperties', True)
        if extra is False:
            assert set(value) <= set(props), where
        for k,v in value.items():
            child = props.get(k, extra if isinstance(extra,dict) else {})
            validate(v,child,whole,where+'.'+k)
    if isinstance(value,list):
        assert len(value) >= schema.get('minItems',0), where
        if 'maxItems' in schema:assert len(value) <= schema['maxItems'], where
        for i,v in enumerate(value):
            validate(v,schema.get('items',{}),whole,where+f'[{i}]')
    if isinstance(value,str):
        assert len(value) >= schema.get('minLength',0), where
        if 'pattern' in schema:
            assert re.search(schema['pattern'],value),where
    if type(value) is int and 'minimum' in schema:
        assert value >= schema['minimum'],where
