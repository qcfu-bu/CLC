SYNTAX:
- syntax0 : raw syntax for parsing
- syntax1 : abstraction (with meta vars)
- syntax2 : annotated (no meta vars)
- syntax3 : case trees

TRANS:
- trans01 : variable binding and infix precedence
- trans12 : implicit argument resolution, function type annotation, initial typechecking
- trans23 : linear typechecking, case tree elaboration
- trans3e : evaluation