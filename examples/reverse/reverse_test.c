// run with dynamically checked ghost code


list* reverse_wrapper(list* ln, lst* l) {
    assert(list_repr(ln, l));
    list* __result = reverse(ln, l);
    assert(list_repr(__result, rev(l)));
    return __result;
}