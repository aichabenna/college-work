function image_RVB = ecriture_RVB(image_originale)
canalR = image_originale(1:2:end, 2:2:end);
canalB = image_originale(2:2:end, 1:2:end);
canalV1 = image_originale(1:2:end, 1:2:end);
canalV2 = image_originale(2:2:end, 2:2:end);
canalV = (canalV1 + canalV2)/2;
image_RVB = cat(3, canalR, canalV, canalB);
end