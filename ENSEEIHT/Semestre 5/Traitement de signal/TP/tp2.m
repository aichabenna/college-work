%%%%%%%%% Génération du signal à filtrer %%%%%%%%%%%
N= 100;
f1 = 1000;
f2 = 3000;
Fe = 10000;
Te = 1/Fe;

% 0 début Te Pas (n-1)*Te Fin
t = [0:Te:(N-1)*Te];

x1 = cos (2*pi*f1*t);
x2 = cos (2*pi*f2*t);

x = x1 + x2;

figure;
subplot(2,1,1);
plot(t,x);
xlabel("Temps en s");
ylabel("x");

Zp = 2^(nextpow2(length(x)));
TF = fft(x, Zp);
subplot(2,1,2);
f = [0: Fe/(Zp-1) :Fe];
semilogy(f, abs(TF));
xlabel("Fréquence en Hz");
ylabel("X");
% Piques à f1 f2 Fe-f2 Fe-f1

%%%%%% Synthèse du filtre passe-bas %%%%%%%%%%
fc = f1;
fc_b= fc/Fe;

ordre1 =11;
h1 = 2 * fc_b * sinc(2* fc_b * [-(ordre1 -1)/2:(ordre1 -1)/2 ])
figure;
subplot(2,2,1);
plot([-(ordre1 -1)/2:(ordre1 -1)/2 ],h1);
xlabel("Fréquence en Hz");
ylabel("h");

ordre2 =61;
h2 = 2 * fc_b * sinc(2* fc_b * [-(ordre2 -1)/2:(ordre2 -1)/2 ])
subplot(2,2,3);
plot([-(ordre2 -1)/2:(ordre2 -1)/2 ],h2);
xlabel("Fréquence en Hz");
ylabel("h");

TF1 = fft(h1, Zp); 
f1 = [0: Fe/(Zp-1) :Fe];
subplot(2,2,2);
semilogy(f1,abs(TF1));
xlabel("Fréquence en Hz");
ylabel("h");

TF2 = fft(h2, Zp); 
f2 = [0: Fe/(Zp-1) :Fe];
subplot(2,2,4);
semilogy(f2,abs(TF2));
xlabel("Fréquence en Hz");
ylabel("h");

%%%%%%%% Réalisation du filtrage %%%%%%%%%%%

figure;
semilogy(f, abs(TF));
hold on;
semilogy(f1,abs(TF1));
hold on;
semilogy(f2,abs(TF2));

y1 = filter(h1, 1, x);
TFY1 = fft(y1, Zp);
figure;
subplot(2,1,1);
semilogy(f, abs(TF));
hold on;
semilogy(f1,abs(TFY1));
hold on;
semilogy(f1,abs(TF1));

y2 = filter(h2, 1, x);
TFY2 = fft(y2, Zp);
subplot(2,1,2);
semilogy(f, abs(TF));
hold on;
semilogy(f2,abs(TFY2));
hold on;
semilogy(f2,abs(TF2));
