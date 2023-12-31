local m = {}

local function factorial(n)
    if n <= 1 then
        return 1
    elseif m[n] then
        return m[n]
    else
        m[n] = n * factorial(n - 1)
        return m[n]
    end
end

local pi = 0

for k = 0, 19 do
    pi = pi + ((-1)^k * factorial(6*k) * (545140134*k+13591409)) / (factorial(3*k) * factorial(k)^3 * (640320^(3*k + 3/2)))
end

pi = 1 / (pi * 12)

print(pi)
